use super::categorize::*;
use super::models::*;
use ahash::{HashMap, HashMapExt, HashSet, HashSetExt};
use osmpbf::{Element, ElementReader};
use std::path::Path;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct WayId(pub i64);
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct NodeId(pub i64);

// Way as represented in OpenStreetMap
struct Way {
    id: WayId,
    nodes: Vec<NodeId>,
    properties: EdgeProperties,
    tags: HashMap<String, String>,
}

impl Default for Way {
    fn default() -> Self {
        Self {
            id: WayId(0),
            nodes: vec![],
            properties: EdgeProperties::default(),
            tags: HashMap::default(),
        }
    }
}

#[derive(Default)]
pub struct Reader {
    nodes: HashMap<NodeId, Node>,
    ways: Vec<Way>,
    nodes_to_keep: HashSet<NodeId>,
    forbidden_tags: HashMap<String, HashSet<String>>,
    required_tags: HashMap<String, HashSet<String>>,
    tags_to_read: HashSet<String>,
    should_merge_ways: bool,
}

impl Reader {
    pub fn new() -> Reader {
        Reader::default()
    }

    pub fn reject(mut self, key: &str, value: &str) -> Self {
        self.forbidden_tags
            .entry(key.to_string())
            .or_default()
            .insert(value.to_string());
        self
    }

    pub fn require(mut self, key: &str, value: &str) -> Self {
        self.required_tags
            .entry(key.to_string())
            .or_default()
            .insert(value.to_string());
        self
    }

    pub fn read_tag(mut self, key: &str) -> Self {
        self.tags_to_read.insert(key.to_string());
        self
    }

    pub fn merge_ways(mut self) -> Self {
        self.should_merge_ways = true;
        self
    }

    fn count_nodes_uses(&mut self) {
        for way in &self.ways {
            for (i, node_id) in way.nodes.iter().enumerate() {
                let node = self
                    .nodes
                    .get_mut(node_id)
                    .unwrap_or_else(|| panic!("Missing node, id: {}", node_id.0));
                // Count double extremities nodes to be sure to include dead-ends
                if i == 0 || i == way.nodes.len() - 1 {
                    node.uses += 2;
                } else {
                    node.uses += 1;
                }
            }
        }
    }

    fn split_way(&self, way: &Way) -> Vec<Edge> {
        let mut result = Vec::new();

        let mut source = NodeId(0);
        let mut geometry = Vec::new();
        let mut nodes = Vec::new();
        for (i, &node_id) in way.nodes.iter().enumerate() {
            let node = self.nodes[&node_id];
            geometry.push(node.coord);
            nodes.push(node.id);
            if i == 0 {
                source = node_id;
            } else if node.uses > 1 {
                result.push(Edge {
                    id: format!("{}-{}", way.id.0, result.len()),
                    osm_id: way.id,
                    source,
                    target: node_id,
                    geometry,
                    properties: way.properties,
                    nodes,
                    tags: way.tags.clone(),
                });

                source = node_id;
                geometry = vec![node.coord];
                nodes = vec![node.id]
            }
        }
        result
    }

    // An OSM way can be split even if it’s — in a topologicial sense — the same edge
    // For instance a road crossing a river, will be split to allow a tag bridge=yes
    // Even if there was no crossing
    fn do_merge_edges(&mut self, edges: Vec<Edge>) -> Vec<Edge> {
        let initial_edges_count = edges.len();

        // We build an adjacency map for every node that might have exactly two edges
        let mut neighbors: HashMap<NodeId, Vec<_>> = HashMap::new();
        for edge in &edges {
            // Extremities of a way in `count_nodes_uses` are counted twice to avoid pruning deadends.
            // We want to look at nodes with at two extremities, hence 4 uses
            if !self.nodes.contains_key(&edge.source) {
                println!("Problem with node {}, edge {}", &edge.source.0, edge.id);
            }
            if self.nodes.get(&edge.source).unwrap().uses == 4 {
                neighbors.entry(edge.source).or_default().push(edge);
            }
            if self.nodes.get(&edge.target).unwrap().uses == 4 {
                neighbors.entry(edge.target).or_default().push(edge);
            }
        }

        let mut result = Vec::new();
        let mut already_merged = HashSet::new();
        for (node, edges) in neighbors.drain() {
            // We merge two edges at the node if there are only two edges
            // The edges must have the same accessibility properties
            // If the consummer asked to store the tags, the tags must be the same for both edges
            // The edges must be from different ways (no surface)
            // The edges must not have been merged this iteration (they might be re-merged through a recurive call)
            if edges.len() == 2
                && edges[0].properties == edges[1].properties
                && edges[0].tags == edges[1].tags
                && edges[0].id != edges[1].id
                && !already_merged.contains(&edges[0].id)
                && !already_merged.contains(&edges[1].id)
            {
                let edge1 = edges[0];
                let edge2 = edges[1];
                result.push(Edge::merge(edge1, edge2, node));
                already_merged.insert(edge1.id.clone());
                already_merged.insert(edge2.id.clone());
                self.nodes.remove(&node);
            }
        }

        for edge in edges {
            if !already_merged.contains(&edge.id) {
                result.push(edge);
            }
        }

        // If we reduced the number of edges, that means that we merged edges
        // They might need to be merged again, recursively
        if initial_edges_count > result.len() {
            self.do_merge_edges(result)
        } else {
            result
        }
    }

    fn is_user_rejected(&self, way: &osmpbf::Way) -> bool {
        let meet_required_tags = self.required_tags.is_empty()
            || way.tags().any(|(key, val)| {
                self.required_tags
                    .get(key)
                    .map(|values| values.contains(val) || values.contains("*"))
                    == Some(true)
            });

        let has_forbidden_tags = way.tags().any(|(key, val)| {
            self.forbidden_tags
                .get(key)
                .map(|vals| vals.contains(val) || vals.contains("*"))
                == Some(true)
        });

        !meet_required_tags || has_forbidden_tags
    }

    fn read_ways(&mut self, file: std::fs::File) {
        let pbf = ElementReader::new(file);

        let result = pbf.par_map_reduce(
            // Mapper function
            |obj| {
                let mut ways_to_add = Vec::new();
                let mut nodes_to_keep = HashSet::new();

                if let Element::Way(way) = obj {
                    let mut properties = EdgeProperties::default();
                    let mut tags = HashMap::new();

                    for (key, val) in way.tags() {
                        properties.update_with_str(key, val);
                        if self.tags_to_read.contains(key) {
                            tags.insert(key.to_string(), val.to_string());
                        }
                    }

                    properties.normalize();

                    let is_rejected = &self.is_user_rejected(&way);

                    if properties.accessible() && !is_rejected {
                        for node in way.refs() {
                            nodes_to_keep.insert(NodeId(node));
                        }
                        ways_to_add.push(Way {
                            id: WayId(way.id()),
                            nodes: way.refs().map(NodeId).collect(),
                            properties,
                            tags,
                        });
                    }
                }

                (ways_to_add, nodes_to_keep)
            },
            // Identity for empty results
            || (Vec::new(), HashSet::new()),
            // Reducer function
            |(mut acc_ways, mut acc_nodes), (ways, nodes)| {
                acc_ways.extend(ways);
                acc_nodes.extend(nodes);
                (acc_ways, acc_nodes)
            },
        );

        // Apply the collected changes
        let (ways_to_add, nodes_to_keep) = result.unwrap();
        self.ways = ways_to_add;
        self.nodes_to_keep = nodes_to_keep;
    }

    fn read_nodes(&mut self, file: std::fs::File) {
        let pbf = ElementReader::new(file);
        self.nodes.reserve(self.nodes_to_keep.len());

        let result = pbf.par_map_reduce(
            // Mapper function
            |obj| {
                let mut nodes_to_insert = HashMap::new();
                let mut ids_to_remove = Vec::new();

                match obj {
                    Element::Node(node) => {
                        let node_id = NodeId(node.id());
                        if self.nodes_to_keep.contains(&node_id) {
                            ids_to_remove.push(node_id);
                            nodes_to_insert.insert(
                                node_id,
                                Node {
                                    id: node_id,
                                    coord: geo_types::Coord {
                                        x: node.lon(),
                                        y: node.lat(),
                                    },
                                    uses: 0,
                                },
                            );
                        }
                    }
                    Element::DenseNode(node) => {
                        let node_id = NodeId(node.id());
                        if self.nodes_to_keep.contains(&node_id) {
                            ids_to_remove.push(node_id);
                            nodes_to_insert.insert(
                                node_id,
                                Node {
                                    id: node_id,
                                    coord: geo_types::Coord {
                                        x: node.lon(),
                                        y: node.lat(),
                                    },
                                    uses: 0,
                                },
                            );
                        }
                    }
                    _ => (),
                }

                (nodes_to_insert, ids_to_remove)
            },
            // Identity for empty results
            || (HashMap::new(), Vec::new()),
            // Reducer function
            |(mut acc_nodes, mut acc_ids), (nodes, ids)| {
                acc_nodes.extend(nodes);
                acc_ids.extend(ids);
                (acc_nodes, acc_ids)
            },
        );

        // Apply the collected changes
        let (nodes_to_insert, ids_to_remove) = result.unwrap();
        for id in ids_to_remove {
            self.nodes_to_keep.remove(&id);
        }
        self.nodes.extend(nodes_to_insert);
    }

    fn nodes(&self) -> Vec<Node> {
        self.nodes
            .values()
            .filter(|node| node.uses > 1)
            .copied()
            .collect()
    }

    fn edges(&self) -> Vec<Edge> {
        self.ways
            .iter()
            .flat_map(|way| self.split_way(way))
            .collect()
    }

    pub fn read<P: AsRef<Path>>(&mut self, filename: P) -> Result<(Vec<Node>, Vec<Edge>), String> {
        let file = std::fs::File::open(filename.as_ref()).map_err(|e| e.to_string())?;
        self.read_ways(file);
        let file_nodes = std::fs::File::open(filename.as_ref()).map_err(|e| e.to_string())?;
        self.read_nodes(file_nodes);
        self.count_nodes_uses();

        let edges = if self.should_merge_ways {
            self.do_merge_edges(self.edges())
        } else {
            self.edges()
        };
        Ok((self.nodes(), edges))
    }
}

// Read all the nodes and ways of the osm.pbf file
pub fn read<P: AsRef<Path>>(filename: P) -> Result<(Vec<Node>, Vec<Edge>), String> {
    Reader::new().read(filename)
}

#[test]
fn test_real_all() {
    let (nodes, ways) = read("src/osm4routing/test_data/minimal.osm.pbf").unwrap();
    assert_eq!(2, nodes.len());
    assert_eq!(1, ways.len());
}

#[test]
fn test_count_nodes() {
    let ways = vec![Way {
        nodes: vec![NodeId(1), NodeId(2), NodeId(3)],
        ..Default::default()
    }];
    let mut nodes = HashMap::new();
    nodes.insert(NodeId(1), Node::default());
    nodes.insert(NodeId(2), Node::default());
    nodes.insert(NodeId(3), Node::default());
    let mut r = Reader {
        nodes,
        ways,
        ..Default::default()
    };
    r.count_nodes_uses();
    assert_eq!(2, r.nodes[&NodeId(1)].uses);
    assert_eq!(1, r.nodes[&NodeId(2)].uses);
    assert_eq!(2, r.nodes[&NodeId(3)].uses);

    assert_eq!(2, r.nodes().len());
}

#[test]
fn test_split() {
    let mut nodes = HashMap::new();
    nodes.insert(NodeId(1), Node::default());
    nodes.insert(NodeId(2), Node::default());
    nodes.insert(NodeId(3), Node::default());
    nodes.insert(NodeId(4), Node::default());
    nodes.insert(NodeId(5), Node::default());
    let ways = vec![
        Way {
            nodes: vec![NodeId(1), NodeId(2), NodeId(3)],
            ..Default::default()
        },
        Way {
            nodes: vec![NodeId(4), NodeId(5), NodeId(2)],
            ..Default::default()
        },
    ];
    let mut r = Reader {
        nodes,
        ways,
        ..Default::default()
    };
    r.count_nodes_uses();
    let edges = r.edges();
    assert_eq!(3, edges.len());
}

#[test]
fn test_wrong_file() {
    let r = read("i hope you have no file name like this one");
    assert!(r.is_err());
}

#[test]
fn forbidden_values() {
    let (_, ways) = Reader::new()
        .reject("highway", "secondary")
        .read("src/osm4routing/test_data/minimal.osm.pbf")
        .unwrap();
    assert_eq!(0, ways.len());
}

#[test]
fn forbidden_wildcard() {
    let (_, ways) = Reader::new()
        .reject("highway", "*")
        .read("src/osm4routing/test_data/minimal.osm.pbf")
        .unwrap();
    assert_eq!(0, ways.len());
}

#[test]
fn way_of_node() {
    let mut r = Reader::new();
    let (_nodes, edges) = r.read("src/osm4routing/test_data/minimal.osm.pbf").unwrap();

    assert_eq!(2, edges[0].nodes.len());
}

#[test]
fn read_tags() {
    let (_nodes, edges) = Reader::new()
        .read_tag("highway")
        .read("src/osm4routing/test_data/minimal.osm.pbf")
        .unwrap();

    assert_eq!("secondary", edges[0].tags.get("highway").unwrap());
}

#[test]
fn require_value_ok() {
    let (_, ways) = Reader::new()
        .require("highway", "secondary")
        .read("src/osm4routing/test_data/minimal.osm.pbf")
        .unwrap();
    assert_eq!(1, ways.len());
}

#[test]
fn require_value_missing() {
    let (_, ways) = Reader::new()
        .require("highway", "primary")
        .read("src/osm4routing/test_data/minimal.osm.pbf")
        .unwrap();
    assert_eq!(0, ways.len());
}

#[test]
fn require_wildcart() {
    let (_, ways) = Reader::new()
        .require("highway", "*")
        .read("src/osm4routing/test_data/minimal.osm.pbf")
        .unwrap();
    assert_eq!(1, ways.len());
}

#[test]
fn require_multiple_tags() {
    let (_, ways) = Reader::new()
        .require("highway", "primary")
        .require("highway", "secondary")
        .read("src/osm4routing/test_data/minimal.osm.pbf")
        .unwrap();
    assert_eq!(1, ways.len());
}

#[test]
fn merging_edges() {
    let (_nodes, edges) = Reader::new()
        .read("src/osm4routing/test_data/ways_to_merge.osm.pbf")
        .unwrap();
    assert_eq!(2, edges.len());

    let (_nodes, edges) = Reader::new()
        .merge_ways()
        .read("src/osm4routing/test_data/ways_to_merge.osm.pbf")
        .unwrap();
    assert_eq!(1, edges.len());
}
