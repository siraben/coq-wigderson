// Wigderson's Algorithm Implementation
class WigdersonAlgorithm {
    constructor() {
        this.graph = null;
        this.coloring = {};
        this.steps = [];
        this.currentStep = -1;
        this.colorPalette = [
            '#FF6B6B', '#4ECDC4', '#45B7D1', '#FFA07A', '#98D8C8',
            '#F7DC6F', '#BB8FCE', '#85C1E2', '#F8B739', '#52B788',
            '#E74C3C', '#3498DB', '#2ECC71', '#F39C12', '#9B59B6',
            '#1ABC9C', '#E67E22', '#34495E', '#95A5A6', '#D35400'
        ];
        this.phase1Colors = 0;
        this.animationSpeed = 500;
    }

    // Generate a 3-colorable graph
    generate3ColorableGraph(n) {
        // Create three partitions for guaranteed 3-colorability
        const partitions = [[], [], []];
        const nodes = [];
        const edges = [];
        
        // Distribute nodes among partitions
        for (let i = 0; i < n; i++) {
            const partition = i % 3;
            partitions[partition].push(i);
            nodes.push({
                id: i,
                partition: partition,
                x: 0,
                y: 0,
                degree: 0,
                color: null
            });
        }
        
        // Add edges only between different partitions
        for (let i = 0; i < n; i++) {
            for (let j = i + 1; j < n; j++) {
                const partition_i = i % 3;
                const partition_j = j % 3;
                
                // Only add edges between different partitions
                if (partition_i !== partition_j) {
                    // Add edge with some probability to vary density
                    if (Math.random() < 0.4) {
                        edges.push({
                            source: i,
                            target: j
                        });
                        nodes[i].degree++;
                        nodes[j].degree++;
                    }
                }
            }
        }
        
        // Ensure the graph is connected
        for (let p = 0; p < 2; p++) {
            if (partitions[p].length > 0 && partitions[p + 1].length > 0) {
                const v1 = partitions[p][0];
                const v2 = partitions[p + 1][0];
                
                // Check if edge already exists
                const edgeExists = edges.some(e => 
                    (e.source === v1 && e.target === v2) || 
                    (e.source === v2 && e.target === v1)
                );
                
                if (!edgeExists) {
                    edges.push({
                        source: v1,
                        target: v2
                    });
                    nodes[v1].degree++;
                    nodes[v2].degree++;
                }
            }
        }
        
        this.graph = {
            nodes: nodes,
            edges: edges,
            adjacencyList: this.buildAdjacencyList(nodes, edges)
        };
        
        return this.graph;
    }
    
    buildAdjacencyList(nodes, edges) {
        const adj = {};
        nodes.forEach(node => {
            adj[node.id] = new Set();
        });
        
        edges.forEach(edge => {
            adj[edge.source].add(edge.target);
            adj[edge.target].add(edge.source);
        });
        
        return adj;
    }
    
    // Get high-degree threshold (floor(sqrt(n)))
    getThreshold() {
        return Math.floor(Math.sqrt(this.graph.nodes.length));
    }
    
    // Find high-degree vertices (original degrees, for initial display)
    findHighDegreeVertices() {
        const threshold = this.getThreshold();
        return this.graph.nodes.filter(node => node.degree > threshold);
    }
    
    // Find high-degree vertices in the remaining graph (dynamic)
    findRemainingHighDegreeVertices(processedVertices = null) {
        const threshold = this.getThreshold();
        const processed = processedVertices || new Set(Object.keys(this.coloring).map(Number));
        
        return this.graph.nodes.filter(node => {
            if (processed.has(node.id)) return false;
            
            // Count degree only among unprocessed vertices
            let remainingDegree = 0;
            for (const neighbor of this.graph.adjacencyList[node.id]) {
                if (!processed.has(neighbor)) {
                    remainingDegree++;
                }
            }
            
            return remainingDegree > threshold;
        });
    }
    
    // Two-color a subgraph (BFS-based bipartite coloring)
    twoColorSubgraph(vertices, color1, color2) {
        if (vertices.length === 0) return {};
        
        const coloring = {};
        const visited = new Set();
        
        // Handle potentially disconnected components in the neighborhood
        for (const startVertex of vertices) {
            if (visited.has(startVertex)) continue;
            
            const queue = [startVertex];
            coloring[startVertex] = color1;
            visited.add(startVertex);
            
            while (queue.length > 0) {
                const current = queue.shift();
                const currentColor = coloring[current];
                const nextColor = currentColor === color1 ? color2 : color1;
                
                for (const neighbor of this.graph.adjacencyList[current]) {
                    if (vertices.includes(neighbor)) {
                        if (!visited.has(neighbor)) {
                            coloring[neighbor] = nextColor;
                            visited.add(neighbor);
                            queue.push(neighbor);
                        } else if (coloring[neighbor] === currentColor) {
                            // Graph is not bipartite - shouldn't happen with proper 3-colorable graph
                            console.warn('Warning: Non-bipartite neighborhood detected');
                            return null;
                        }
                    }
                }
            }
        }
        
        return coloring;
    }
    
    // Phase 1: Color high-degree vertices and their neighborhoods
    phase1() {
        // Keep finding high-degree vertices until none remain
        const processedVertices = new Set();
        const phase1Coloring = {};
        let i = 0; // Color counter, following the algorithm notation
        const k = this.getThreshold(); // k = floor(sqrt(n))
        
        while (true) {
            // Find the highest-degree vertex in the REMAINING graph
            let maxDegree = -1;
            let highestDegreeVertex = null;
            
            for (const node of this.graph.nodes) {
                if (processedVertices.has(node.id)) continue;
                
                // Count degree only among unprocessed vertices
                let remainingDegree = 0;
                for (const neighbor of this.graph.adjacencyList[node.id]) {
                    if (!processedVertices.has(neighbor)) {
                        remainingDegree++;
                    }
                }
                
                if (remainingDegree > maxDegree) {
                    maxDegree = remainingDegree;
                    highestDegreeVertex = node;
                }
            }
            
            // Check if max degree > k (threshold)
            if (maxDegree <= k) break;
            
            const vertex = highestDegreeVertex;
            
            // Get unprocessed neighborhood
            const neighborhood = Array.from(this.graph.adjacencyList[vertex.id])
                .filter(v => !processedVertices.has(v));
            
            // Two-color the neighborhood with colors i and i+1
            if (neighborhood.length > 0) {
                const neighborColoring = this.twoColorSubgraph(
                    neighborhood, 
                    i, 
                    i + 1
                );
                
                if (neighborColoring) {
                    // Store the coloring
                    Object.assign(phase1Coloring, neighborColoring);
                    
                    this.steps.push({
                        type: 'phase1_neighborhood',
                        phase: 'Phase 1',
                        vertex: vertex.id,
                        neighborhood: neighborhood,
                        coloring: neighborColoring,
                        description: `Two-coloring neighborhood of vertex ${vertex.id} with colors ${i} and ${i + 1}`
                    });
                    
                    // Mark neighborhood vertices as processed
                    neighborhood.forEach(v => processedVertices.add(v));
                }
            }
            
            // Color the high-degree vertex with color i+2
            phase1Coloring[vertex.id] = i + 2;
            
            this.steps.push({
                type: 'phase1_vertex',
                phase: 'Phase 1',
                vertex: vertex.id,
                color: i + 2,
                description: `Coloring high-degree vertex ${vertex.id} with color ${i + 2}`
            });
            
            // Mark the high-degree vertex as processed
            processedVertices.add(vertex.id);
            
            // Increment i by 2 (not 3!) as per the algorithm
            i += 2;
        }
        
        // Phase 1 uses colors 0 through i+2 (the last color used was i+2 from the previous iteration)
        // For Phase 2, we start from color i
        this.phase1Colors = i;
        return { processedVertices, phase1Coloring };
    }
    
    // Phase 2: Color remaining graph with colors i, i+1, i+2, ...
    // Simply assign consecutive colors starting from i
    phase2(processedVertices, phase1Coloring) {
        const remainingVertices = this.graph.nodes
            .filter(v => !processedVertices.has(v.id));
        
        // Start coloring from color i (where Phase 1 left off)
        const i = this.phase1Colors;
        
        // Assign consecutive colors i, i+1, i+2, ... to remaining vertices
        remainingVertices.forEach((vertex, index) => {
            const color = i + index;
            
            this.steps.push({
                type: 'phase2',
                phase: 'Phase 2',
                vertex: vertex.id,
                color: color,
                description: `Coloring vertex ${vertex.id} with color ${color}`
            });
        });
        
        // Phase 2 uses colors i through i + (number of remaining vertices - 1)
    }
    
    // Run the complete algorithm
    runAlgorithm() {
        this.steps = [];
        this.coloring = {};
        this.currentStep = -1;
        
        // Add initial step
        this.steps.push({
            type: 'init',
            phase: 'Initialization',
            description: 'Starting Wigderson\'s algorithm'
        });
        
        // Phase 1
        const { processedVertices, phase1Coloring } = this.phase1();
        
        if (processedVertices.size > 0) {
            this.steps.push({
                type: 'phase_transition',
                phase: 'Transition',
                description: `Phase 1 complete. Colored ${processedVertices.size} vertices. Moving to Phase 2.`
            });
        }
        
        // Phase 2
        this.phase2(processedVertices, phase1Coloring);
        
        this.steps.push({
            type: 'complete',
            phase: 'Complete',
            description: 'Algorithm complete. Graph is colored.'
        });
        
        return this.steps;
    }
    
    // Apply a step to the current coloring
    applyStep(step) {
        switch (step.type) {
            case 'phase1_vertex':
                this.coloring[step.vertex] = step.color;
                break;
            case 'phase1_neighborhood':
                Object.assign(this.coloring, step.coloring);
                break;
            case 'phase2':
                this.coloring[step.vertex] = step.color;
                break;
        }
    }
    
    // Step forward in the algorithm
    stepForward() {
        if (this.currentStep < this.steps.length - 1) {
            this.currentStep++;
            const step = this.steps[this.currentStep];
            this.applyStep(step);
            return step;
        }
        return null;
    }
    
    // Step backward in the algorithm
    stepBackward() {
        if (this.currentStep > 0) {
            // We can go back from any step > 0
            this.currentStep--;
            
            // Rebuild coloring from scratch up to the new currentStep
            this.coloring = {};
            for (let i = 0; i <= this.currentStep; i++) {
                this.applyStep(this.steps[i]);
            }
            
            return this.steps[this.currentStep];
        } else if (this.currentStep === 0) {
            // Going back from step 0 means no steps applied
            this.currentStep = -1;
            this.coloring = {};
            return null;
        }
        // Already at -1, can't go further back
        return null;
    }
    
    // Reset the algorithm
    reset() {
        this.coloring = {};
        this.currentStep = -1;
    }
    
    // Generate detailed debug information
    getDebugInfo() {
        const stats = this.getStatistics();
        let debug = '=== WIGDERSON\'S ALGORITHM DEBUG LOG ===\n\n';
        
        // Graph structure
        debug += '1. GRAPH STRUCTURE\n';
        debug += '-----------------\n';
        debug += `Vertices: ${this.graph.nodes.length}\n`;
        debug += `Edges: ${this.graph.edges.length}\n`;
        debug += `√n = ${stats.sqrtN}\n`;
        debug += `High-degree threshold: > ${stats.threshold}\n\n`;
        
        // Adjacency list
        debug += 'Adjacency List:\n';
        for (let i = 0; i < this.graph.nodes.length; i++) {
            const neighbors = Array.from(this.graph.adjacencyList[i]).sort((a, b) => a - b);
            debug += `  Vertex ${i}: [${neighbors.join(', ')}] (degree: ${neighbors.length})\n`;
        }
        debug += '\n';
        
        // High-degree vertices
        debug += '2. HIGH-DEGREE VERTICES\n';
        debug += '----------------------\n';
        const highDegreeVertices = this.findHighDegreeVertices();
        if (highDegreeVertices.length > 0) {
            highDegreeVertices.forEach(v => {
                debug += `  Vertex ${v.id}: degree ${v.degree}\n`;
            });
        } else {
            debug += '  None (all vertices have degree ≤ √n)\n';
        }
        debug += '\n';
        
        // Algorithm execution steps
        debug += '3. ALGORITHM EXECUTION\n';
        debug += '---------------------\n';
        if (this.steps.length > 0) {
            this.steps.forEach((step, index) => {
                if (step.type === 'init' || step.type === 'phase_transition' || step.type === 'complete') {
                    debug += `\n[Step ${index + 1}] ${step.description}\n`;
                } else if (step.type === 'phase1_vertex') {
                    debug += `[Step ${index + 1}] Phase 1: Colored vertex ${step.vertex} with color ${step.color}\n`;
                } else if (step.type === 'phase1_neighborhood') {
                    debug += `[Step ${index + 1}] Phase 1: Two-colored neighborhood of vertex ${step.vertex}\n`;
                    debug += `  Neighborhood: [${step.neighborhood.join(', ')}]\n`;
                    debug += `  Colors assigned:\n`;
                    for (const [v, c] of Object.entries(step.coloring)) {
                        debug += `    Vertex ${v} -> Color ${c}\n`;
                    }
                } else if (step.type === 'phase2') {
                    debug += `[Step ${index + 1}] Phase 2: Colored vertex ${step.vertex} with color ${step.color}\n`;
                }
            });
        } else {
            debug += 'Algorithm not yet executed.\n';
        }
        debug += '\n';
        
        // Final coloring
        debug += '4. FINAL COLORING\n';
        debug += '----------------\n';
        if (Object.keys(this.coloring).length > 0) {
            const sortedVertices = Object.keys(this.coloring).map(Number).sort((a, b) => a - b);
            sortedVertices.forEach(v => {
                debug += `  Vertex ${v}: Color ${this.coloring[v]}\n`;
            });
            debug += '\n';
            
            // Group by color
            const colorGroups = {};
            for (const [v, c] of Object.entries(this.coloring)) {
                if (!colorGroups[c]) colorGroups[c] = [];
                colorGroups[c].push(Number(v));
            }
            
            debug += 'Vertices grouped by color:\n';
            const sortedColors = Object.keys(colorGroups).map(Number).sort((a, b) => a - b);
            sortedColors.forEach(c => {
                colorGroups[c].sort((a, b) => a - b);
                debug += `  Color ${c}: [${colorGroups[c].join(', ')}]\n`;
            });
        } else {
            debug += 'No vertices colored yet.\n';
        }
        debug += '\n';
        
        // Statistics
        debug += '5. STATISTICS\n';
        debug += '------------\n';
        debug += `Total vertices: ${stats.totalVertices}\n`;
        debug += `Vertices colored: ${stats.verticesColored}\n`;
        debug += `Colors used: ${stats.colorsUsed}\n`;
        debug += `Theoretical bound (3√n): ${stats.theoreticalBound}\n`;
        debug += `Bound satisfied: ${stats.colorsUsed <= stats.theoreticalBound ? 'YES ✓' : 'NO ✗'}\n`;
        
        // Validation
        debug += '\n6. VALIDATION\n';
        debug += '------------\n';
        const validation = this.validateColoring();
        debug += `Total vertices: ${validation.totalVertices}\n`;
        debug += `Vertices colored: ${validation.totalColored}\n`;
        debug += `All vertices colored: ${validation.allColored ? 'YES ✓' : 'NO ✗'}\n`;
        
        if (!validation.allColored && validation.uncoloredVertices.length > 0) {
            debug += `Uncolored vertices: [${validation.uncoloredVertices.join(', ')}]\n`;
        }
        
        debug += `No adjacent vertices with same color: ${validation.noConflicts ? 'YES ✓' : 'NO ✗'}\n`;
        
        if (!validation.noConflicts && validation.conflicts.length > 0) {
            debug += `\nConflicts found (${validation.conflicts.length} total):\n`;
            validation.conflicts.forEach(([u, v]) => {
                const uColor = this.coloring[u];
                const vColor = this.coloring[v];
                debug += `  Edge (${u}, ${v}): both vertices have color ${uColor}\n`;
                
                // Show the adjacency for debugging
                const uNeighbors = Array.from(this.graph.adjacencyList[u]).sort((a, b) => a - b);
                const vNeighbors = Array.from(this.graph.adjacencyList[v]).sort((a, b) => a - b);
                debug += `    Vertex ${u} neighbors: [${uNeighbors.join(', ')}]\n`;
                debug += `    Vertex ${v} neighbors: [${vNeighbors.join(', ')}]\n`;
            });
        }
        
        return debug;
    }
    
    // Validate the coloring
    validateColoring() {
        const result = {
            allColored: true,
            noConflicts: true,
            conflicts: [],
            uncoloredVertices: [],
            totalVertices: this.graph.nodes.length,
            totalColored: 0
        };
        
        // Check if all vertices are colored
        for (let i = 0; i < this.graph.nodes.length; i++) {
            if (this.coloring[i] === undefined || this.coloring[i] === null) {
                result.allColored = false;
                result.uncoloredVertices.push(i);
            } else {
                result.totalColored++;
            }
        }
        
        // Check for conflicts using adjacency list
        // We check each edge exactly once by checking both directions
        const checkedPairs = new Set();
        
        for (let v = 0; v < this.graph.nodes.length; v++) {
            const vColor = this.coloring[v];
            
            // Skip if this vertex is not colored
            if (vColor === undefined || vColor === null) continue;
            
            // Check all neighbors
            for (const neighbor of this.graph.adjacencyList[v]) {
                const nColor = this.coloring[neighbor];
                
                // Skip if neighbor is not colored
                if (nColor === undefined || nColor === null) continue;
                
                // Create a unique key for this edge (smaller vertex first)
                const edgeKey = v < neighbor ? `${v}-${neighbor}` : `${neighbor}-${v}`;
                
                // Skip if we've already checked this edge
                if (checkedPairs.has(edgeKey)) continue;
                checkedPairs.add(edgeKey);
                
                // Check for conflict
                if (vColor === nColor) {
                    result.noConflicts = false;
                    result.conflicts.push([Math.min(v, neighbor), Math.max(v, neighbor)]);
                }
            }
        }
        
        return result;
    }
    
    // Get current statistics
    getStatistics() {
        const highDegreeVertices = this.findHighDegreeVertices();
        const colorSet = new Set(Object.values(this.coloring));
        const n = this.graph.nodes.length;
        const sqrtN = Math.ceil(Math.sqrt(n));
        // Wigderson's algorithm uses at most 3*sqrt(n) colors
        // More precisely: O(sqrt(n)) but the constant is 3
        const theoreticalBound = 3 * Math.ceil(Math.sqrt(n));
        
        return {
            totalVertices: n,
            threshold: this.getThreshold(),
            highDegreeCount: highDegreeVertices.length,
            colorsUsed: colorSet.size,
            verticesColored: Object.keys(this.coloring).length,
            theoreticalBound: theoreticalBound,
            sqrtN: sqrtN
        };
    }
}

// Visualization Controller
class Visualization {
    constructor(algorithm) {
        this.algorithm = algorithm;
        this.svg = d3.select('#graph');
        this.width = 800;
        this.height = 600;
        this.simulation = null;
        this.showDegrees = true;
    }
    
    initGraph() {
        this.svg.selectAll('*').remove();
        
        // Add arrow markers for directed edges (though graph is undirected)
        this.svg.append('defs').selectAll('marker')
            .data(['end'])
            .enter().append('marker')
            .attr('id', String)
            .attr('viewBox', '0 -5 10 10')
            .attr('refX', 15)
            .attr('refY', 0)
            .attr('markerWidth', 6)
            .attr('markerHeight', 6)
            .attr('orient', 'auto')
            .append('path')
            .attr('d', 'M0,-5L10,0L0,5')
            .attr('fill', '#999');
        
        // Create groups for edges and nodes
        this.linkGroup = this.svg.append('g').attr('class', 'links');
        this.nodeGroup = this.svg.append('g').attr('class', 'nodes');
        
        this.updateGraph();
    }
    
    updateGraph() {
        const graph = this.algorithm.graph;
        if (!graph) return;
        
        // Update links
        const links = this.linkGroup.selectAll('line')
            .data(graph.edges, d => `${d.source}-${d.target}`);
        
        links.enter().append('line')
            .attr('stroke', '#999')
            .attr('stroke-opacity', 0.6)
            .attr('stroke-width', 2)
            .merge(links);
        
        links.exit().remove();
        
        // Update nodes
        const nodes = this.nodeGroup.selectAll('g')
            .data(graph.nodes, d => d.id);
        
        const nodeEnter = nodes.enter().append('g')
            .attr('class', 'node')
            .call(d3.drag()
                .on('start', (event, d) => this.dragStarted(event, d))
                .on('drag', (event, d) => this.dragged(event, d))
                .on('end', (event, d) => this.dragEnded(event, d)));
        
        nodeEnter.append('circle')
            .attr('r', d => {
                // Smaller nodes for larger graphs
                const n = this.algorithm.graph.nodes.length;
                if (n <= 20) return 20;
                if (n <= 50) return 15;
                return 10;
            })
            .attr('fill', '#ddd')
            .attr('stroke', '#333')
            .attr('stroke-width', 2);
        
        nodeEnter.append('text')
            .attr('text-anchor', 'middle')
            .attr('dy', '.35em')
            .attr('font-size', d => {
                // Smaller text for larger graphs
                const n = this.algorithm.graph.nodes.length;
                if (n <= 20) return '12px';
                if (n <= 50) return '10px';
                return '8px';
            })
            .attr('font-weight', 'bold')
            .text(d => d.id);
        
        // Add degree label
        nodeEnter.append('text')
            .attr('class', 'degree-label')
            .attr('text-anchor', 'middle')
            .attr('dy', '-1.2em')  // Slightly above the vertex
            .attr('font-size', '9px')
            .attr('fill', '#666')
            .attr('font-weight', 'bold');
        
        // Update node colors and rings based on current coloring
        const processedVertices = new Set(Object.keys(this.algorithm.coloring).map(Number));
        
        this.nodeGroup.selectAll('g.node').select('circle')
            .attr('fill', d => {
                const color = this.algorithm.coloring[d.id];
                return color !== undefined ? this.algorithm.colorPalette[color % this.algorithm.colorPalette.length] : '#ddd';
            })
            .attr('stroke-width', d => {
                // Check if this vertex is high-degree in the REMAINING graph
                const remainingHighDegree = this.algorithm.findRemainingHighDegreeVertices();
                const isHighDegree = remainingHighDegree.some(node => node.id === d.id);
                return isHighDegree ? 4 : 2;
            })
            .attr('stroke', d => {
                // Check if this vertex is high-degree in the REMAINING graph
                const remainingHighDegree = this.algorithm.findRemainingHighDegreeVertices();
                const isHighDegree = remainingHighDegree.some(node => node.id === d.id);
                return isHighDegree ? '#ff0000' : '#333';
            });
        
        // Update degree labels to show remaining degree
        this.nodeGroup.selectAll('g.node').select('.degree-label')
            .text(d => {
                // Check if degrees should be shown
                if (!this.showDegrees) return '';
                
                // Don't show degree for colored vertices
                if (processedVertices.has(d.id)) return '';
                
                // Calculate remaining degree
                let remainingDegree = 0;
                for (const neighbor of this.algorithm.graph.adjacencyList[d.id]) {
                    if (!processedVertices.has(neighbor)) {
                        remainingDegree++;
                    }
                }
                
                // Just show the number
                return remainingDegree;
            })
            .attr('fill', d => {
                // Color the degree label red if it's high-degree
                const remainingHighDegree = this.algorithm.findRemainingHighDegreeVertices();
                const isHighDegree = remainingHighDegree.some(node => node.id === d.id);
                return isHighDegree ? '#ff0000' : '#666';
            });
        
        nodes.exit().remove();
        
        // Initialize or restart simulation with adjusted parameters for larger graphs
        const n = graph.nodes.length;
        const nodeRadius = n <= 20 ? 30 : (n <= 50 ? 20 : 15);
        const linkDistance = n <= 20 ? 100 : (n <= 50 ? 80 : 60);
        const chargeStrength = n <= 20 ? -300 : (n <= 50 ? -200 : -100);
        
        if (!this.simulation) {
            this.simulation = d3.forceSimulation(graph.nodes)
                .force('link', d3.forceLink(graph.edges).id(d => d.id).distance(linkDistance))
                .force('charge', d3.forceManyBody().strength(chargeStrength))
                .force('center', d3.forceCenter(this.width / 2, this.height / 2))
                .force('collision', d3.forceCollide().radius(nodeRadius));
        } else {
            this.simulation.nodes(graph.nodes);
            this.simulation.force('link').links(graph.edges).distance(linkDistance);
            this.simulation.force('charge').strength(chargeStrength);
            this.simulation.force('collision').radius(nodeRadius);
            this.simulation.alpha(0.3).restart();
        }
        
        this.simulation.on('tick', () => this.ticked());
    }
    
    ticked() {
        this.linkGroup.selectAll('line')
            .attr('x1', d => d.source.x)
            .attr('y1', d => d.source.y)
            .attr('x2', d => d.target.x)
            .attr('y2', d => d.target.y);
        
        this.nodeGroup.selectAll('g.node')
            .attr('transform', d => `translate(${d.x},${d.y})`);
    }
    
    dragStarted(event, d) {
        if (!event.active) this.simulation.alphaTarget(0.3).restart();
        d.fx = d.x;
        d.fy = d.y;
    }
    
    dragged(event, d) {
        d.fx = event.x;
        d.fy = event.y;
    }
    
    dragEnded(event, d) {
        if (!event.active) this.simulation.alphaTarget(0);
        d.fx = null;
        d.fy = null;
    }
    
    highlightStep(step) {
        // Reset all highlights
        this.nodeGroup.selectAll('g.node').select('circle')
            .classed('highlighted', false)
            .classed('selected-high-degree', false)
            .attr('stroke-dasharray', null);
        
        // Update the red rings to show current high-degree vertices
        this.updateGraph();
        
        // Highlight relevant nodes based on step type
        if (step.type === 'phase1_vertex') {
            // Highlight the selected high-degree vertex with a special style
            this.nodeGroup.selectAll('g.node')
                .filter(d => d.id === step.vertex)
                .select('circle')
                .classed('selected-high-degree', true)
                .attr('stroke', '#ff00ff')  // Magenta for selected high-degree vertex
                .attr('stroke-width', 6)
                .attr('stroke-dasharray', '5,5');
        } else if (step.type === 'phase1_neighborhood') {
            // Highlight the high-degree vertex being processed
            const vertex = step.vertex;
            this.nodeGroup.selectAll('g.node')
                .filter(d => d.id === vertex)
                .select('circle')
                .classed('selected-high-degree', true)
                .attr('stroke', '#ff00ff')  // Magenta for selected high-degree vertex
                .attr('stroke-width', 6);
            
            // Highlight the neighborhood being colored
            this.nodeGroup.selectAll('g.node')
                .filter(d => step.neighborhood.includes(d.id))
                .select('circle')
                .classed('highlighted', true)
                .attr('stroke-dasharray', '5,5');
        } else if (step.type === 'phase2') {
            this.nodeGroup.selectAll('g.node')
                .filter(d => d.id === step.vertex)
                .select('circle')
                .classed('highlighted', true)
                .attr('stroke-dasharray', '5,5');
        }
    }
}

// Main Application Controller
class App {
    constructor() {
        this.algorithm = new WigdersonAlgorithm();
        this.visualization = new Visualization(this.algorithm);
        this.isRunning = false;
        this.showDegrees = true; // Toggle for degree display
        this.currentAlgorithmLine = 0;
        this.initEventListeners();
        this.initAlgorithmDisplay();
        this.generateNewGraph();
    }
    
    initAlgorithmDisplay() {
        const algorithmHTML = `
            <div class="algorithm-line" data-line="0"><strong>Algorithm 1</strong> Wigderson's 3-coloring algorithm</div>
            <div class="algorithm-line" data-line="0"><strong>Input:</strong> A 3-colorable graph $G(V,E)$</div>
            <div class="algorithm-line" data-line="1">1: $n \\leftarrow |V|$, $k \\leftarrow \\lfloor\\sqrt{n}\\rfloor$</div>
            <div class="algorithm-line" data-line="2">2: $i \\leftarrow 0$</div>
            <div class="algorithm-line" data-line="3">3: <strong>while</strong> $\\text{max\_degree}(G) > k$ <strong>do</strong></div>
            <div class="algorithm-line" data-line="4" style="margin-left: 20px;">4: $v \\leftarrow$ highest-degree vertex in $G$</div>
            <div class="algorithm-line" data-line="5" style="margin-left: 20px;">5: $H \\leftarrow$ subgraph of $G$ induced by neighborhood $N_G(v)$</div>
            <div class="algorithm-line" data-line="6" style="margin-left: 20px;">6: 2-color $H$ with colors $i, i+1$</div>
            <div class="algorithm-line" data-line="7" style="margin-left: 20px;">7: color $v$ with color $i+2$</div>
            <div class="algorithm-line" data-line="8" style="margin-left: 20px;">8: $i \\leftarrow i+2$</div>
            <div class="algorithm-line" data-line="9" style="margin-left: 20px;">9: $G \\leftarrow$ subgraph of $G$ after deleting $N_G(v) \\cup \\{v\\}$</div>
            <div class="algorithm-line" data-line="10">10: <strong>end while</strong></div>
            <div class="algorithm-line" data-line="11">11: color $G$ with colors $i, i+1, i+2, \\ldots$ and halt</div>
        `;
        
        document.getElementById('algorithmText').innerHTML = algorithmHTML;
        
        // Trigger MathJax to render
        if (window.MathJax) {
            window.MathJax.typesetPromise();
        }
    }
    
    updateAlgorithmHighlight(step) {
        // Remove all highlights
        document.querySelectorAll('.algorithm-line').forEach(line => {
            line.classList.remove('current');
        });
        
        // Determine which line to highlight based on step
        let lineToHighlight = 0;
        
        if (!step) {
            lineToHighlight = 0;
        } else if (step.type === 'init') {
            lineToHighlight = 1; // Line 1: n ← |V|
        } else if (step.type === 'phase1_vertex') {
            // When selecting and coloring high-degree vertex
            lineToHighlight = 7; // Line 7: color v with color i+2
        } else if (step.type === 'phase1_neighborhood') {
            // When coloring the neighborhood
            lineToHighlight = 6; // Line 6: 2-color H with colors i, i+1
        } else if (step.type === 'phase_transition') {
            lineToHighlight = 10; // Line 10: end while
        } else if (step.type === 'phase2') {
            lineToHighlight = 11; // Line 11: color G with colors i, i+1, ...
        } else if (step.type === 'complete') {
            lineToHighlight = 11; // Line 11: halt
        }
        
        // For phase 1 steps, we might want to show the loop
        if (step && (step.type === 'phase1_vertex' || step.type === 'phase1_neighborhood')) {
            // Also highlight line 3 to show we're in the while loop
            const line3 = document.querySelector('.algorithm-line[data-line="3"]');
            if (line3) line3.classList.add('current');
        }
        
        // Highlight the specific line
        const line = document.querySelector(`.algorithm-line[data-line="${lineToHighlight}"]`);
        if (line) {
            line.classList.add('current');
            line.scrollIntoView({ behavior: 'smooth', block: 'nearest' });
        }
    }
    
    initEventListeners() {
        document.getElementById('generateGraph').addEventListener('click', () => this.generateNewGraph());
        document.getElementById('reset').addEventListener('click', () => this.reset());
        document.getElementById('stepForward').addEventListener('click', () => this.stepForward());
        document.getElementById('stepBack').addEventListener('click', () => this.stepBackward());
        document.getElementById('runAll').addEventListener('click', () => this.runAll());
        document.getElementById('debugLog').addEventListener('click', () => this.showDebugLog());
        document.getElementById('toggleDegree').addEventListener('click', () => this.toggleDegrees());
        
        const verticesSlider = document.getElementById('vertices');
        const verticesInput = document.getElementById('verticesInput');
        
        // Sync slider and input
        verticesSlider.addEventListener('input', (e) => {
            verticesInput.value = e.target.value;
        });
        verticesSlider.addEventListener('change', () => this.generateNewGraph());
        
        verticesInput.addEventListener('input', (e) => {
            const value = Math.max(5, Math.min(100, parseInt(e.target.value) || 10));
            verticesInput.value = value;
            verticesSlider.value = value;
        });
        verticesInput.addEventListener('change', () => this.generateNewGraph());
        
        const speedSlider = document.getElementById('speed');
        speedSlider.addEventListener('input', (e) => {
            document.getElementById('speedValue').textContent = e.target.value + 'ms';
            this.algorithm.animationSpeed = parseInt(e.target.value);
        });
        
        // Modal event listeners
        const modal = document.getElementById('debugModal');
        const closeBtn = document.getElementsByClassName('close')[0];
        
        closeBtn.addEventListener('click', () => {
            modal.style.display = 'none';
        });
        
        window.addEventListener('click', (e) => {
            if (e.target === modal) {
                modal.style.display = 'none';
            }
        });
        
        document.getElementById('copyDebug').addEventListener('click', () => this.copyDebugToClipboard());
        document.getElementById('downloadDebug').addEventListener('click', () => this.downloadDebugLog());
    }
    
    generateNewGraph() {
        const n = parseInt(document.getElementById('verticesInput').value);
        this.algorithm.generate3ColorableGraph(n);
        this.algorithm.runAlgorithm();
        this.visualization.initGraph();
        this.reset();
        this.updateStatistics();
        this.updateColorLegend();
    }
    
    toggleDegrees() {
        this.showDegrees = !this.showDegrees;
        this.visualization.showDegrees = this.showDegrees;
        this.visualization.updateGraph();
        
        // Update button text
        const btn = document.getElementById('toggleDegree');
        btn.textContent = this.showDegrees ? 'Hide Degrees' : 'Show Degrees';
    }
    
    reset() {
        this.algorithm.reset();
        this.visualization.updateGraph();
        this.updateUI();
        this.clearStepLog();
        document.getElementById('currentPhase').textContent = 'Not Started';
        document.getElementById('phaseDescription').textContent = '';
        this.updateAlgorithmHighlight(null);
    }
    
    stepForward() {
        const step = this.algorithm.stepForward();
        if (step) {
            this.visualization.updateGraph();
            this.visualization.highlightStep(step);
            this.updateUI();
            this.addStepToLog(step);
            this.updatePhaseInfo(step);
            this.updateAlgorithmHighlight(step);
        }
    }
    
    stepBackward() {
        const step = this.algorithm.stepBackward();
        this.visualization.updateGraph();
        if (step) {
            this.visualization.highlightStep(step);
        }
        this.updateUI();
        this.removeLastStepFromLog();
        if (step) {
            this.updatePhaseInfo(step);
            this.updateAlgorithmHighlight(step);
        } else {
            document.getElementById('currentPhase').textContent = 'Not Started';
            document.getElementById('phaseDescription').textContent = '';
            this.updateAlgorithmHighlight(null);
        }
    }
    
    async runAll() {
        if (this.isRunning) return;
        this.isRunning = true;
        
        const button = document.getElementById('runAll');
        button.textContent = 'Running...';
        button.disabled = true;
        
        while (this.algorithm.currentStep < this.algorithm.steps.length - 1) {
            this.stepForward();
            await new Promise(resolve => setTimeout(resolve, this.algorithm.animationSpeed));
            
            if (!this.isRunning) break;
        }
        
        button.textContent = 'Run All Steps';
        button.disabled = false;
        this.isRunning = false;
    }
    
    updateUI() {
        this.updateStatistics();
        
        // Update button states
        document.getElementById('stepBack').disabled = this.algorithm.currentStep < 0;
        document.getElementById('stepForward').disabled = this.algorithm.currentStep >= this.algorithm.steps.length - 1;
    }
    
    updateStatistics() {
        const stats = this.algorithm.getStatistics();
        document.getElementById('totalVertices').textContent = stats.totalVertices;
        document.getElementById('sqrtN').textContent = stats.sqrtN;
        document.getElementById('threshold').textContent = stats.threshold;
        document.getElementById('highDegreeCount').textContent = stats.highDegreeCount;
        document.getElementById('colorsUsed').textContent = stats.colorsUsed;
        document.getElementById('theoreticalBound').textContent = stats.theoreticalBound;
        document.getElementById('verticesColored').textContent = stats.verticesColored;
    }
    
    updatePhaseInfo(step) {
        document.getElementById('currentPhase').textContent = step.phase;
        document.getElementById('phaseDescription').textContent = step.description;
    }
    
    addStepToLog(step) {
        const log = document.getElementById('stepLog');
        const li = document.createElement('li');
        li.textContent = `Step ${this.algorithm.currentStep + 1}: ${step.description}`;
        log.appendChild(li);
        log.scrollTop = log.scrollHeight;
    }
    
    removeLastStepFromLog() {
        const log = document.getElementById('stepLog');
        if (log.lastChild) {
            log.removeChild(log.lastChild);
        }
    }
    
    clearStepLog() {
        document.getElementById('stepLog').innerHTML = '';
    }
    
    updateColorLegend() {
        const legend = document.getElementById('colorLegend');
        legend.innerHTML = '';
        
        // Get unique colors used
        const maxColors = 20; // Show first 20 colors
        for (let i = 0; i < Math.min(maxColors, this.algorithm.colorPalette.length); i++) {
            const colorDiv = document.createElement('div');
            colorDiv.className = 'color-item';
            colorDiv.innerHTML = `
                <span class="color-box" style="background-color: ${this.algorithm.colorPalette[i]}"></span>
                <span>Color ${i}</span>
            `;
            legend.appendChild(colorDiv);
        }
    }
    
    showDebugLog() {
        const modal = document.getElementById('debugModal');
        const debugContent = document.getElementById('debugContent');
        
        // Generate and display debug information
        debugContent.textContent = this.algorithm.getDebugInfo();
        modal.style.display = 'block';
    }
    
    copyDebugToClipboard() {
        const debugContent = document.getElementById('debugContent').textContent;
        
        // Create a temporary textarea to copy from
        const textarea = document.createElement('textarea');
        textarea.value = debugContent;
        document.body.appendChild(textarea);
        textarea.select();
        
        try {
            document.execCommand('copy');
            
            // Show feedback
            const copyBtn = document.getElementById('copyDebug');
            const originalText = copyBtn.textContent;
            copyBtn.textContent = 'Copied!';
            setTimeout(() => {
                copyBtn.textContent = originalText;
            }, 2000);
        } catch (err) {
            console.error('Failed to copy:', err);
        }
        
        document.body.removeChild(textarea);
    }
    
    downloadDebugLog() {
        const debugContent = document.getElementById('debugContent').textContent;
        const timestamp = new Date().toISOString().replace(/[:.]/g, '-');
        const filename = `wigderson-debug-${timestamp}.txt`;
        
        // Create a blob with the debug content
        const blob = new Blob([debugContent], { type: 'text/plain' });
        const url = URL.createObjectURL(blob);
        
        // Create a download link and click it
        const a = document.createElement('a');
        a.href = url;
        a.download = filename;
        document.body.appendChild(a);
        a.click();
        document.body.removeChild(a);
        
        // Clean up the URL
        URL.revokeObjectURL(url);
    }
}

// Initialize the application
document.addEventListener('DOMContentLoaded', () => {
    new App();
});
