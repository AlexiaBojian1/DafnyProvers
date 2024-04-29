/**
  * has_cycle 
  * @author Andrei Tudor Popescu | ID: 1668161
  * @author Alexia Bojian | ID: 1708112
  */

// This exercise is about cycle detection in a directed graph
// see the description on Canvas.

// The type Node models natural numbers in the range 0 .. N-1.
type nat' = n: nat | n > 0 witness 1
const N: nat'
type Node = n: nat | 0 <= n < N

// The type Graph models a directed graph. If G is a Graph, then
// G.Keys contains the vertices, and the successors of Node u are given by G[u].
const EmptyGraph := map i: Node :: []
type Graph = g: map<Node, seq<Node>> | forall i: Node :: i in g.Keys witness EmptyGraph

// Path is a sequence of nodes.
type Path = p: seq<Node> | |p| > 0 witness [0]

// A GraphColoring is a mapping that assign colors to nodes.
datatype Color = Black | Gray | White
type GraphColoring = map<Node, Color>

class HasCycleAlgorithm
  {
  const G: Graph
  var coloring: GraphColoring
  ghost var call_stack: Path  // The call stack of the recursion.

  // Assigns numbers to colors.
  ghost function ColorValue(c: Color): nat
  {
    match c
    case Black => 0
    case Gray => 1
    case White => 2
  }

  // The sum of the color values is used to prove termination.
  ghost function ColorSum(coloring: GraphColoring): nat
  {
    if |coloring| == 0
    then 0
    else
      var u: Node :| u in coloring;
      ColorValue(coloring[u]) + ColorSum(coloring - {u})
  }

  // There is a directed edge from u to v in G.
  ghost predicate IsEdge(u: Node, v: Node)
  {
    v in G[u]
  }

  // The sequence of nodes p is a path in the graph G.
  ghost predicate IsPath(p: Path)
  {
    forall i | 0 <= i < |p| - 1 :: IsEdge(p[i], p[i+1])
  }

  // The sequence of nodes p is a cycle in the graph G.
  ghost predicate IsCycle(p: Path)
  {
    IsPath(p) && |p| > 1 && p[0] == p[|p|-1]
  }

  // The graph G contains a cycle.
  ghost predicate HasCycle()
  {
    exists p: Path :: IsCycle(p)
  }

  // Successors of a black node are black.
  ghost predicate SuccessorsOfBlackNodesAreBlack()
    reads this
    requires coloring.Keys == G.Keys
  {
    forall u: Node :: coloring[u] == Black ==> forall v | v in G[u] :: coloring[v] == Black
  }

  // All gray nodes are contained in `call_stack`.
  ghost predicate GrayNodesAreOnStack()
    reads this
    requires coloring.Keys == G.Keys
  {
    forall u: Node | u in G :: coloring[u] == Gray ==> u in call_stack
  }

  // Our witness for a cycle is a `lasso`, which consists of a path p from u to v,
  // followed by a cycle q from v to v.
  ghost predicate IsLasso(u: Node, v: Node, p: Path, q: Path)
    requires IsPath(p)
    requires IsPath(q)
  {
    p[0] == u && p[|p|-1] == q[0] == v && IsCycle(q)
  }

  // There is a lasso starting in u.
  ghost predicate HasCycleFrom(u: Node)
  {
    exists p: Path, q: Path, v: Node | IsPath(p) && IsPath(q) && v in G :: IsLasso(u, v, p, q)
  }

  // See also https://leino.science/papers/krml274.html
  lemma ColorSumLemma(coloring: GraphColoring, u: Node)
    requires u in coloring
    ensures ColorSum(coloring) == ColorSum(coloring - {u}) + ColorValue(coloring[u])
  {
    var x: Node :| x in coloring && ColorSum(coloring) == ColorSum(coloring - {x}) + ColorValue(coloring[x]);
    if x == u {

    } else {
      calc {
        ColorSum(coloring);
        {/* def sum */}
        ColorSum(coloring - {x}) + ColorValue(coloring[x]);
        {ColorSumLemma(coloring - {x}, u);}
        ColorValue(coloring[x]) + ColorValue(coloring[u]) + ColorSum(coloring - {x} - {u});
        {assert coloring - {x} - {u} == coloring - {u} - {x};}
        ColorValue(coloring[u]) + ColorValue(coloring[x]) + ColorSum(coloring - {u} - {x});
        {ColorSumLemma(coloring - {u}, x);}
        ColorSum(coloring - {u}) + ColorValue(coloring[u]);
      }
    }
  }

  lemma ComplexCycleLemma(u: Node)
    requires forall v: Node | v in G[u] :: !HasCycleFrom(v)
    requires G[u] != []
    ensures !HasCycleFrom(u)
  {
    if(HasCycleFrom(u)) {

      calc {
        assert HasCycleFrom(u);
        exists p: Path, q: Path, v: Node | IsPath(p) && IsPath(q) && v in G :: IsLasso(u, v, p, q);
        exists p: Path, q: Path, v: Node | IsPath(p) && |p| > 2 && IsPath(q) && v in G :: IsLasso(u, v, p, q) && p[1] in G[u];
        exists p: Path, q: Path, v: Node | IsPath(p) && |p| > 2 && IsPath(q) && v in G :: IsLasso(u, v, p, q) && p[1] in G[u] && IsLasso(p[1], v, p[1..], q);
        exists p: Path, q: Path, v: Node | IsPath(p) && IsEdge(u, p[0]) && |p| > 1 && IsPath(q) && v in G :: IsLasso(u, v, p, q);
        exists p: Path, q: Path, v: Node | IsPath(p) && |p| > 2 && IsPath(q) && v in G && p[0] in G[u] && IsLasso(u, v, p, q) && p[1] in G[u] :: IsLasso(p[0], v, p, q);
        exists v: Node | v in G[u] :: HasCycleFrom(v);
        false;
      }
      assert !HasCycleFrom(u);
    }
  }

  // If there is no cycle reachable from the successors of u, then there is
  // no cycle reachable from u.
  lemma CycleLemma(u: Node)
    requires forall v: Node | v in G[u] :: !HasCycleFrom(v)
    ensures !HasCycleFrom(u)
  {
    if G[u] == [] {
      assert !exists p: Path | |p| > 2 :: u == p[0] && IsEdge(p[0], p[1]) && IsEdge(p[1], p[2]);
    }
    else {
      ComplexCycleLemma(u);
    }
  }

  lemma BiggerEqualsColorLemma(u: Node)
    requires coloring.Keys == G.Keys
    ensures ColorSum(coloring[u := Black]) <= ColorSum(coloring)
  {
    var newColoring := coloring[u := Black];
    assert (coloring - {u}) == (newColoring - {u});
    assert ColorSum(coloring - {u}) == ColorSum(newColoring - {u});
    ColorSumLemma(coloring, u);
    ColorSumLemma(newColoring, u);
    assert ColorSum(newColoring) == ColorSum(coloring) - ColorValue(coloring[u]);
  }

  lemma BiggerColorLemma(u: Node)
    requires coloring.Keys == G.Keys
    requires coloring[u] == White
    ensures ColorSum(coloring[u := Gray]) < ColorSum(coloring)
  {
    var newColoring := coloring[u := Gray];
    assert (coloring - {u}) == (newColoring - {u});
    ColorSumLemma(coloring, u);
    ColorSumLemma(newColoring, u);
    assert ColorSum(newColoring) < ColorSum(coloring);
  }

  lemma ChildCycleLemma(u: Node, v: Node)
    requires HasCycleFrom(v)
    requires v in G[u]
    ensures HasCycleFrom(u)
  {
    assert exists p: Path, q: Path, w: Node | IsPath(p) && IsPath(q) && w in G :: IsLasso(v, w, p, q);
    assert exists p: Path, q: Path, w: Node | IsPath(p) && IsPath(q) && w in G :: IsLasso(v, w, p, q) && IsLasso(u, w, [u] + p, q);
    assert HasCycleFrom(u);
  } 

  lemma CallStackLemma(u: Node, v: Node)
    requires call_stack[|call_stack| - 1] == u
    requires v in call_stack
    requires IsPath(call_stack)
    requires v in G[u]
    ensures HasCycleFrom(u)
  {
    var i: nat :| 0 <= i < |call_stack| && call_stack[i] == v;
    var new_call_stack := call_stack + [v];
    assert IsLasso(u, v, [u] + [v], new_call_stack[i..]);
  }

  // Checks if there is a cycle in G in the nodes reachable from u.
  method dfs(u: Node) returns (found: bool)
    modifies this
    decreases ColorSum(coloring)
    requires coloring.Keys == G.Keys
    requires coloring[u] == White
    requires |call_stack| > 0
    requires IsPath(call_stack)
    requires call_stack[|call_stack| - 1] == u
    requires GrayNodesAreOnStack()
    requires SuccessorsOfBlackNodesAreBlack()
    requires forall v: Node | v in G :: coloring[v] == Black ==> !HasCycleFrom(v)

    ensures coloring.Keys == old(coloring.Keys)
    ensures call_stack == old(call_stack)
    ensures forall v: Node | v in coloring.Keys :: ColorValue(coloring[v]) <= old(ColorValue(coloring[v]))
    ensures ColorValue(coloring[u]) < ColorValue(old(coloring)[u])
    ensures ColorSum(coloring) < ColorSum(old(coloring))
    ensures SuccessorsOfBlackNodesAreBlack()
    ensures forall v: Node | v in G :: coloring[v] == Black ==> !HasCycleFrom(v)
    ensures !found ==> GrayNodesAreOnStack()
    ensures !found ==> coloring[u] == Black
    ensures found <==> HasCycleFrom(u)
  {
    BiggerColorLemma(u);
    //assume ColorSum(coloring[u := Gray]) < ColorSum(coloring);  // assume (1)
    coloring := coloring[u := Gray];
    assert coloring[u] == Gray;

    var successors := G[u];

    var i: nat := 0;
    while i < |successors|
      invariant 0 <= i <= |successors|
      invariant call_stack == old(call_stack)
      invariant call_stack[|call_stack| - 1] == u
      invariant coloring.Keys == old(coloring.Keys)
      invariant forall v: Node | v in coloring.Keys :: ColorValue(coloring[v]) <= old(ColorValue(coloring[v]))
      invariant ColorValue(coloring[u]) < old(ColorValue(coloring[u]))
      invariant ColorSum(coloring) < ColorSum(old(coloring))
      invariant GrayNodesAreOnStack()
      invariant SuccessorsOfBlackNodesAreBlack()
      invariant forall v: Node | v in coloring.Keys :: coloring[v] == Black ==> !HasCycleFrom(v)
      invariant forall k | 0 <= k < i :: coloring[successors[k]] == Black
    {
      var v := successors[i];
      if coloring[v] == White
      {
        call_stack := call_stack + [v];
        var result := dfs(v);
        call_stack := call_stack[0 .. |call_stack| - 1];
        ColorSumLemma(coloring, u);
        //assume ColorSum(old(coloring)) < ColorSum(coloring);  // assume (2)
        if result
        {
          ChildCycleLemma(u, v);
          // assume HasCycleFrom(u);  // assume (3)
          return true;
        }
      }
      else if coloring[v] == Gray
      {
        CallStackLemma(u, v);
        // assume HasCycleFrom(u);  // assume (4)
        return true;
      }
      i := i + 1;
    }
    CycleLemma(u);
    BiggerEqualsColorLemma(u);
    //assume ColorSum(coloring[u := Black]) <= ColorSum(coloring);  // assume (5)
    coloring := coloring[u := Black];

    return false;
  }

  // Checks if there is a cycle in G.
  method has_cycle() returns (found: bool)
    modifies this
    ensures found <==> HasCycle()
  {
    coloring := map u | u in G :: White;

    var nodes := G.Keys;
    while nodes != {}
      invariant coloring.Keys == G.Keys
      invariant GrayNodesAreOnStack()
      invariant SuccessorsOfBlackNodesAreBlack()
      invariant forall v: Node | v in G :: coloring[v] == Black ==> !HasCycleFrom(v)
      invariant !exists v: Node | v in G :: coloring[v] == Gray
      invariant forall u: Node | u !in nodes :: (forall v | v in G[u] :: coloring[v] == Black) && coloring[u] == Black
      invariant forall u: Node | u !in nodes && coloring[u] == Black :: forall p: Path | IsPath(p) && p[0] == u && |p| > 1 :: coloring[p[1]] == Black
    {
      var u :| u in nodes;
      nodes := nodes - {u};

      if coloring[u] == White
      {
        call_stack := [u];

        found := dfs(u);
        if found
        {
          return true;
        }
      }
    }
    assert SuccessorsOfBlackNodesAreBlack();
    assert forall v: Node | v in G :: coloring[v] == Black;
    return false;
  }
}
