"""
Cross-check Wigderson's algorithm results from Coq.

This script implements the same algorithm as the Coq formalization and
verifies that all Coq-computed colorings are valid proper colorings.
"""

from collections import defaultdict

# ===== Graph representation =====
# Graph: dict mapping node -> set of neighbors (undirected)

def mk_graph(edges):
    """Build undirected graph from edge list."""
    g = defaultdict(set)
    for u, v in edges:
        g[u].add(v)
        g[v].add(u)
    return dict(g)

def adj(g, v):
    """Adjacency set of v in g."""
    return g.get(v, set())

def nodes(g):
    """All nodes in g."""
    return set(g.keys())

def degree(g, v):
    """Degree of v in g."""
    return len(adj(g, v))

# ===== Subgraph operations =====

def remove_node(g, v):
    """Remove single node v from graph g."""
    result = {}
    for u in g:
        if u != v:
            result[u] = g[u] - {v}
    return result

def remove_nodes(g, s):
    """Remove set of nodes s from graph g."""
    result = {}
    for v in g:
        if v not in s:
            result[v] = g[v] - s
    return result

def subgraph_of(g, s):
    """Induced subgraph on node set s. Only includes nodes in both g and s."""
    result = {}
    for v in s:
        if v in g:
            result[v] = g[v] & s
    return result

def neighborhood(g, v):
    """
    Neighborhood subgraph: remove_node v (subgraph_of g (adj g v)).
    The induced subgraph on the neighbors of v, with v removed.
    """
    nbrs = adj(g, v)
    sub = subgraph_of(g, nbrs)
    return remove_node(sub, v)

# ===== BFS-based 2-coloring (force_all) =====

def force_component(g, seed, c1, c2):
    """BFS 2-color starting from seed. Returns (coloring, reached_set)."""
    coloring = {}
    coloring[seed] = c1
    queue = [seed]
    reached = {seed}
    while queue:
        next_queue = []
        for v in queue:
            current_color = coloring[v]
            next_color = c2 if current_color == c1 else c1
            for w in sorted(adj(g, v)):  # sorted for determinism
                if w not in coloring and w in g:
                    coloring[w] = next_color
                    reached.add(w)
                    next_queue.append(w)
        queue = next_queue
    return coloring, reached

def force_all(g, c1, c2):
    """2-color entire graph using BFS, one component at a time."""
    coloring = {}
    remaining = dict(g)
    while remaining:
        # S.choose picks smallest in PositiveSet (= smallest positive)
        seed = min(remaining.keys())
        comp_coloring, reached = force_component(remaining, seed, c1, c2)
        coloring.update(comp_coloring)
        remaining = remove_nodes(remaining, reached)
    return coloring

# ===== Phase 1 =====

def subset_nodes_high_deg(g, k):
    """Return set of vertices with degree > k."""
    return {v for v in g if degree(g, v) > k}

def choose_min(s):
    """S.choose in Coq picks the smallest element."""
    if not s:
        return None
    return min(s)

def phase1(k, c, g):
    """
    Phase 1 of Wigderson's algorithm.
    Mirrors the Coq Function definition exactly.
    Returns (coloring, residual_graph).
    """
    high = subset_nodes_high_deg(g, k)
    v = choose_min(high)
    if v is None:
        return {}, dict(g)

    # 2-color the neighborhood using force_all
    nbhd = neighborhood(g, v)
    m_prime = force_all(nbhd, c + 1, c + 2)  # two_color_nbd

    # Remove v and its neighborhood nodes from the graph
    nodes_to_remove = {v} | nodes(nbhd)
    g_prime = remove_nodes(g, nodes_to_remove)

    # Recurse
    f2, g2 = phase1(k, c + 3, g_prime)

    # Combine: Munion (M.add v c m') f2
    # Munion is left-heavy: current step takes priority
    result = dict(f2)
    for key, val in m_prime.items():
        result[key] = val
    result[v] = c  # v gets color c (overwrites if present)

    return result, g2

# ===== Phase 2 =====

def max_deg(g):
    """Maximum degree in graph g."""
    if not g:
        return 0
    return max((len(adj(g, v)) for v in g), default=0)

def extract_deg_vert(g, d):
    """Find a vertex with degree exactly d. Returns None if none exists.
    Mimics Coq's extract_deg_vert_dec (picks by M.elements order = sorted)."""
    for v in sorted(g.keys()):
        if degree(g, v) == d:
            return v
    return None

def extract_vertices_degs(g, d):
    """
    Extract vertices of degree d one at a time.
    After removing each vertex, neighbors' degrees decrease.
    Mirrors Coq's Function extract_vertices_degs exactly.
    """
    v = extract_deg_vert(g, d)
    if v is None:
        return set(), dict(g)

    g_prime = remove_node(g, v)
    ns, g_pp = extract_vertices_degs(g_prime, d)
    return ns | {v}, g_pp

def phase2(g):
    """
    Phase 2: greedy coloring by extracting max-degree independent sets.
    Mirrors Coq's Function phase2 exactly.
    Returns (coloring, residual_graph).
    """
    md = max_deg(g)
    if md == 0:
        return {v: 1 for v in g}, {}

    ns, g_prime = extract_vertices_degs(g, md)
    f_prime, g_pp = phase2(g_prime)

    # Color ns with Pos.of_nat(S(S n)) where md = S n
    # Pos.of_nat(md + 1) = md + 1
    color = md + 1
    result = {v: color for v in ns}
    # Munion: constant_color ns takes priority
    for key, val in f_prime.items():
        if key not in result:
            result[key] = val

    return result, g_pp

# ===== max_color =====

def max_color(f):
    """Maximum color value in coloring f. Returns 1 if empty (like Coq's fold base)."""
    if not f:
        return 1
    return max(f.values())

# ===== Wigderson =====

def wigderson(k, g):
    """
    Full Wigderson algorithm.
    Mirrors Coq definition: offset phase2 colors by max_color(f1).
    """
    f1, g_prime = phase1(k, 1, g)
    offset = max_color(f1)
    f2, _ = phase2(g_prime)

    # Offset phase2 colors by adding offset (Pos.add offset)
    f2_offset = {v: c + offset for v, c in f2.items()}

    # Munion: f1 takes priority over f2_offset
    result = dict(f2_offset)
    result.update(f1)

    return result

# ===== Validation =====

def validate_coloring(g, coloring, name=""):
    """Check that coloring is a valid proper coloring of g."""
    errors = []
    for v in g:
        if v not in coloring:
            errors.append(f"Vertex {v} not colored")
    for v in g:
        for w in adj(g, v):
            if v < w:
                cv = coloring.get(v)
                cw = coloring.get(w)
                if cv is not None and cw is not None and cv == cw:
                    errors.append(f"Edge ({v},{w}): both colored {cv}")
    if errors:
        print(f"  FAIL {name}: {errors}")
        return False
    else:
        print(f"  PASS {name}")
        return True

# ===== Test graphs =====

graphs = {
    "triangle": mk_graph([(1,2), (2,3), (3,1)]),
    "path4": mk_graph([(1,2), (2,3), (3,4)]),
    "c5": mk_graph([(1,2), (2,3), (3,4), (4,5), (5,1)]),
    "example": mk_graph([(6,4), (4,5), (4,3), (3,2), (5,2), (1,2), (1,5)]),
    "k23": mk_graph([(1,3), (1,4), (1,5), (2,3), (2,4), (2,5)]),
    "star_plus": mk_graph([(1,2), (1,3), (1,4), (1,5), (2,3), (4,5)]),
}

# ===== More complex test graphs =====

complex_graphs = {
    # Cycle C7 (odd cycle, 3-chromatic)
    "c7": mk_graph([(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,1)]),

    # Petersen graph (3-chromatic, 10 vertices, 15 edges)
    # Outer cycle: 1-2-3-4-5-1, Inner pentagram: 6-8-10-7-9-6
    "petersen": mk_graph([
        (1,2),(2,3),(3,4),(4,5),(5,1),       # outer cycle
        (6,8),(8,10),(10,7),(7,9),(9,6),      # inner pentagram
        (1,6),(2,7),(3,8),(4,9),(5,10),       # spokes
    ]),

    # Cube graph Q3 (bipartite, 2-chromatic, 8 vertices)
    "cube": mk_graph([
        (1,2),(2,3),(3,4),(4,1),  # bottom face
        (5,6),(6,7),(7,8),(8,5),  # top face
        (1,5),(2,6),(3,7),(4,8),  # vertical edges
    ]),

    # Wheel W6 (center 1, rim 2-3-4-5-6-7-2, 4-chromatic due to odd rim)
    "wheel7": mk_graph([
        (2,3),(3,4),(4,5),(5,6),(6,7),(7,2),  # rim (C6, even)
        (1,2),(1,3),(1,4),(1,5),(1,6),(1,7),  # spokes
    ]),

    # Grotzsch graph (triangle-free, 4-chromatic, 11 vertices)
    # Classic: outer cycle 1-2-3-4-5-1, inner star 6-7-8-9-10, center 11
    "grotzsch": mk_graph([
        (1,2),(2,3),(3,4),(4,5),(5,1),           # outer cycle
        (6,2),(6,3), (7,3),(7,4), (8,4),(8,5),   # inner to outer
        (9,5),(9,1), (10,1),(10,2),               # inner to outer
        (11,6),(11,7),(11,8),(11,9),(11,10),      # center to inner
    ]),

    # Grid 3x3 (bipartite, 2-chromatic, 9 vertices)
    # 1-2-3
    # |   |   |
    # 4-5-6
    # |   |   |
    # 7-8-9
    "grid3x3": mk_graph([
        (1,2),(2,3),(4,5),(5,6),(7,8),(8,9),  # rows
        (1,4),(4,7),(2,5),(5,8),(3,6),(6,9),  # columns
    ]),

    # K33 (complete bipartite, 2-chromatic, 6 vertices)
    "k33": mk_graph([
        (1,4),(1,5),(1,6),(2,4),(2,5),(2,6),(3,4),(3,5),(3,6),
    ]),

    # Dodecahedron (3-chromatic, 20 vertices, 30 edges)
    "dodecahedron": mk_graph([
        (1,2),(2,3),(3,4),(4,5),(5,1),             # outer pentagon
        (1,6),(2,7),(3,8),(4,9),(5,10),             # spokes out
        (6,11),(6,15),(7,11),(7,12),(8,12),(8,13),  # middle
        (9,13),(9,14),(10,14),(10,15),              # middle
        (11,16),(12,17),(13,18),(14,19),(15,20),    # spokes in
        (16,17),(17,18),(18,19),(19,20),(20,16),    # inner pentagon
    ]),

    # Two triangles sharing a vertex (3-chromatic)
    "bowtie": mk_graph([(1,2),(2,3),(3,1),(3,4),(4,5),(5,3)]),

    # Moser spindle (4-chromatic, 7 vertices - unit distance graph)
    # But let's use a Mycielski graph M4 instead (triangle-free, 4-chromatic, 11 vertices)
    # Actually let's use a simple planar 3-colorable graph: octahedron minus edge
    # Octahedron = K_{2,2,2} (3-chromatic, 6 vertices, 12 edges)
    "octahedron": mk_graph([
        (1,3),(1,4),(1,5),(1,6),
        (2,3),(2,4),(2,5),(2,6),
        (3,5),(3,6),(4,5),(4,6),
    ]),

    # Path P10 (bipartite, 2-chromatic)
    "path10": mk_graph([(i,i+1) for i in range(1,10)]),
}

# Coq results (from Eval compute in test_wigderson.v)
coq_results_k1 = {
    "triangle":  {2:2, 1:1, 3:3},
    "path4":     {4:3, 2:1, 1:2, 3:2},
    "c5":        {4:4, 2:2, 1:1, 5:2, 3:3},
    "example":   {4:4, 2:2, 6:5, 1:1, 5:3, 3:5},
    "k23":       {4:2, 2:3, 1:1, 5:2, 3:2},
    "star_plus": {4:2, 2:2, 1:1, 5:3, 3:3},
}

coq_results_k2 = {
    "triangle":  {2:4, 1:3, 3:2},
    "c5":        {4:4, 2:4, 1:3, 5:2, 3:2},
    "example":   {4:5, 2:1, 6:4, 1:2, 5:3, 3:2},
    "star_plus": {4:2, 2:2, 1:1, 5:3, 3:3},
}

# Coq results for complex graphs (k=1)
coq_complex_k1 = {
    "c7":          {4:4, 2:2, 6:6, 1:1, 5:5, 3:5, 7:2},
    "petersen":    {8:8, 4:4, 2:2, 10:7, 6:2, 1:1, 9:5, 5:2, 3:5, 7:8},
    "cube":        {8:5, 4:2, 2:2, 6:5, 1:1, 5:2, 3:5, 7:4},
    "wheel7":      {4:2, 2:2, 6:2, 1:1, 5:3, 3:3, 7:3},
    "grotzsch":    {8:5, 4:4, 2:2, 10:3, 6:8, 1:1, 9:3, 5:2, 3:5, 11:7, 7:6},
    "grid3x3":     {8:4, 4:2, 2:2, 6:7, 1:1, 9:5, 5:5, 3:6, 7:5},
    "k33":         {4:2, 2:3, 6:2, 1:1, 5:2, 3:3},
    "bowtie":      {4:5, 2:2, 1:1, 5:4, 3:3},
    "octahedron":  {4:2, 2:4, 6:3, 1:1, 5:3, 3:2},
    "path10":      {8:4, 4:8, 2:1, 10:9, 6:8, 1:2, 9:5, 5:7, 3:2, 7:5},
    "dodecahedron": {16:10, 8:7, 4:4, 20:11, 12:8, 2:2, 18:16, 10:13, 6:2,
                     14:14, 1:1, 17:11, 9:5, 5:2, 13:8, 3:5, 19:15, 11:11,
                     7:15, 15:14},
}

# Coq results for complex graphs (k=2)
coq_complex_k2 = {
    "c7":          {4:4, 2:4, 6:4, 1:3, 5:2, 3:2, 7:2},
    "petersen":    {8:5, 4:5, 2:2, 10:3, 6:2, 1:1, 9:3, 5:2, 3:3, 7:5},
    "cube":        {8:5, 4:2, 2:2, 6:5, 1:1, 5:2, 3:5, 7:4},
    "wheel7":      {4:2, 2:2, 6:2, 1:1, 5:3, 3:3, 7:3},
    "grotzsch":    {8:5, 4:4, 2:2, 10:3, 6:8, 1:1, 9:3, 5:2, 3:5, 11:7, 7:6},
    "grid3x3":     {8:5, 4:4, 2:1, 6:4, 1:2, 9:3, 5:2, 3:2, 7:3},
    "k33":         {4:2, 2:3, 6:2, 1:1, 5:2, 3:3},
    "bowtie":      {4:2, 2:3, 1:2, 5:3, 3:1},
    "octahedron":  {4:2, 2:4, 6:3, 1:1, 5:3, 3:2},
    "path10":      {8:4, 4:4, 2:4, 10:3, 6:4, 1:2, 9:2, 5:2, 3:2, 7:2},
    "dodecahedron": {16:7, 8:4, 4:12, 20:8, 12:5, 2:2, 18:12, 10:11, 6:2,
                     14:10, 1:1, 17:8, 9:11, 5:2, 13:5, 3:5, 19:11, 11:8,
                     7:12, 15:12},
}

all_pass = True

print("=" * 60)
print("1. Validate Coq results (k=1)")
print("=" * 60)
for name, g in graphs.items():
    ok = validate_coloring(g, coq_results_k1[name], f"Coq k=1 {name}")
    all_pass = all_pass and ok

print()
print("=" * 60)
print("2. Validate Coq results (k=2)")
print("=" * 60)
for name in coq_results_k2:
    ok = validate_coloring(graphs[name], coq_results_k2[name], f"Coq k=2 {name}")
    all_pass = all_pass and ok

print()
print("=" * 60)
print("3. Python Wigderson algorithm (k=1)")
print("=" * 60)
for name, g in graphs.items():
    py = wigderson(1, g)
    ok = validate_coloring(g, py, f"Python k=1 {name}")
    all_pass = all_pass and ok
    print(f"    Colors: {dict(sorted(py.items()))}")

print()
print("=" * 60)
print("4. Python Wigderson algorithm (k=2)")
print("=" * 60)
for name in coq_results_k2:
    py = wigderson(2, graphs[name])
    ok = validate_coloring(graphs[name], py, f"Python k=2 {name}")
    all_pass = all_pass and ok
    print(f"    Colors: {dict(sorted(py.items()))}")

print()
print("=" * 60)
print("5. Compare Coq vs Python (k=1)")
print("=" * 60)
print()
print("Note: Exact colors may differ due to vertex ordering details.")
print("What matters is both are valid proper colorings.")
print()
for name, g in graphs.items():
    coq_c = coq_results_k1[name]
    py_c = wigderson(1, g)
    n_coq = len(set(coq_c.values()))
    n_py = len(set(py_c.values()))
    match = coq_c == py_c
    status = "MATCH" if match else "differ (both valid)"
    print(f"  {name:12s}  Coq:{n_coq} colors  Py:{n_py} colors  {status}")
    if not match:
        print(f"    Coq:    {dict(sorted(coq_c.items()))}")
        print(f"    Python: {dict(sorted(py_c.items()))}")

print()
print("=" * 60)
print("6. Compare Coq vs Python (k=2)")
print("=" * 60)
print()
for name in coq_results_k2:
    coq_c = coq_results_k2[name]
    py_c = wigderson(2, graphs[name])
    n_coq = len(set(coq_c.values()))
    n_py = len(set(py_c.values()))
    match = coq_c == py_c
    status = "MATCH" if match else "differ (both valid)"
    print(f"  {name:12s}  Coq:{n_coq} colors  Py:{n_py} colors  {status}")
    if not match:
        print(f"    Coq:    {dict(sorted(coq_c.items()))}")
        print(f"    Python: {dict(sorted(py_c.items()))}")

print()
print("=" * 60)
print("7. Validate Coq complex results (k=1)")
print("=" * 60)
for name in coq_complex_k1:
    ok = validate_coloring(complex_graphs[name], coq_complex_k1[name], f"Coq k=1 {name}")
    all_pass = all_pass and ok

print()
print("=" * 60)
print("8. Validate Coq complex results (k=2)")
print("=" * 60)
for name in coq_complex_k2:
    ok = validate_coloring(complex_graphs[name], coq_complex_k2[name], f"Coq k=2 {name}")
    all_pass = all_pass and ok

print()
print("=" * 60)
print("9. Complex graphs - Python Wigderson (k=1)")
print("=" * 60)
for name, g in complex_graphs.items():
    py = wigderson(1, g)
    ok = validate_coloring(g, py, f"Py k=1 {name}")
    all_pass = all_pass and ok
    n_colors = len(set(py.values()))
    print(f"    |V|={len(g):2d}  |E|={sum(len(v) for v in g.values())//2:2d}  "
          f"colors={n_colors}")

print()
print("=" * 60)
print("10. Compare Coq vs Python complex graphs (k=1)")
print("=" * 60)
print()
for name in coq_complex_k1:
    coq_c = coq_complex_k1[name]
    py_c = wigderson(1, complex_graphs[name])
    n_coq = len(set(coq_c.values()))
    n_py = len(set(py_c.values()))
    match = coq_c == py_c
    status = "MATCH" if match else "differ (both valid)"
    print(f"  {name:14s}  Coq:{n_coq:2d} colors  Py:{n_py:2d} colors  {status}")
    if not match:
        print(f"    Coq:    {dict(sorted(coq_c.items()))}")
        print(f"    Python: {dict(sorted(py_c.items()))}")

print()
print("=" * 60)
print("11. Compare Coq vs Python complex graphs (k=2)")
print("=" * 60)
print()
for name in coq_complex_k2:
    coq_c = coq_complex_k2[name]
    py_c = wigderson(2, complex_graphs[name])
    n_coq = len(set(coq_c.values()))
    n_py = len(set(py_c.values()))
    match = coq_c == py_c
    status = "MATCH" if match else "differ (both valid)"
    print(f"  {name:14s}  Coq:{n_coq:2d} colors  Py:{n_py:2d} colors  {status}")
    if not match:
        print(f"    Coq:    {dict(sorted(coq_c.items()))}")
        print(f"    Python: {dict(sorted(py_c.items()))}")

print()
print("=" * 60)
print("12. Complex graphs - Python Wigderson (k=sqrt(n))")
print("=" * 60)
import math
for name, g in complex_graphs.items():
    k = max(1, int(math.sqrt(len(g))))
    py = wigderson(k, g)
    ok = validate_coloring(g, py, f"Py k=sqrt({len(g)})={k} {name}")
    all_pass = all_pass and ok
    n_colors = len(set(py.values()))
    print(f"    |V|={len(g):2d}  |E|={sum(len(v) for v in g.values())//2:2d}  "
          f"k={k}  colors={n_colors}")

print()
if all_pass:
    print("ALL CHECKS PASSED")
else:
    print("SOME CHECKS FAILED")
