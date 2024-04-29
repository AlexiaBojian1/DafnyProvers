/**
  * heapsort 
  * @author Andrei Tudor Popescu | ID: 1668161
  * @author Alexia Bojian | ID: 1708112
  */

predicate sorted(a: array<int>, lo: int, hi: int)
  requires 0 <= lo <= hi <= a.Length
  reads a
{
  forall j, k :: lo <= j < k < hi ==> a[j] <= a[k]
}

predicate isMaxHeap(a: array<int>, h: int)
  requires 0 <= h < a.Length
  reads a
{
  forall i :: 0 < i <= h ==> a[parent(i)] >= a[i]
}

// parent node id in the tree
function parent(i: nat) : int
{
  if i == 0 then 0 else (i - 1) / 2
}

// left child id in the tree
function lchild(i: nat) : nat
  ensures parent(lchild(i)) == i
{ 2 * i + 1 }

// right child id in the tree
function rchild(i: nat) : nat
  ensures parent(rchild(i)) == i
{ 2 * i + 2 }

// a[mx] is the maximum of a[0..n+1]
predicate max(a: seq<int>, n: int, mx: int)
  requires 0 <= mx <= n < |a|
{
  forall i :: 0 <= i <= n ==> a[i] <= a[mx]
}

// the root of a max-heap a,h is the maximum of all heap elements

lemma MaxHeapLemma(a: array<int>, h: int)
  requires 0 <= h < a.Length
  requires isMaxHeap(a, h)
  ensures max(a[..], h, 0)
{
  if(h ==0) {
    return;
  }
  if h == 1 {
    assert a[0] >= a[0];
    assert a[parent(h)] >= a[h];
  } else {
    assert h > 1 ==> a[parent(h)] >= a[h];
    assert h-1 >= 0;
    MaxHeapLemma(a,h-1);
  }
  assert max(a[..],h,0);
}

// turn a into a heap by bubbling up
method {:verify true} Heapify(a: array<int>)
  modifies a
  requires a.Length > 1
  ensures multiset(a[0..]) == multiset(old(a[0..]))
  ensures isMaxHeap(a, a.Length - 1)
{

  var  curr := 0;

  while  curr < a.Length - 1
    invariant  0 <=  curr < a.Length
    invariant isMaxHeap(a, curr)
    invariant multiset(a[0..]) == multiset(old(a[0..]))
    decreases a.Length -  curr
  {
    curr :=  curr + 1;

    ghost var n :=  curr;
    var lastNode :=  curr;
    var theParent := parent(lastNode);

    while lastNode > 0 && a[lastNode] > a[theParent]
      invariant 0 <= lastNode <=  curr
      invariant 0 <= theParent <=  curr
      invariant 1 <=  curr < a.Length
      invariant forall i | 1 <= i <=  curr && i != lastNode :: a[parent(i)] >= a[i]
      invariant forall i | 0 <= i <=  curr && parent(i) == lastNode && lastNode > 0 :: a[parent(parent(i))] >= a[i]
      invariant n ==  curr
      invariant multiset(a[0..]) == multiset(old(a[0..]))
      invariant theParent == parent(lastNode)
      decreases lastNode
    {
      var temp := a[lastNode];
      a[lastNode] := a[theParent];
      a[theParent] := temp;

      lastNode := theParent;
      theParent := parent(lastNode);
    }
  }
}


method swap(a: array<int>, i: int, j: int)
  modifies a
  requires 0 <= i < a.Length && 0 <= j < a.Length
{
  var temp := a[i];
  a[i] := a[j];
  a[j] := temp;
}



// turn a into a sorted array by putting the head of a to the end
// and insert the last element of the heap at the top and bubble it down
method {:verify true} UnHeapify(a: array<int>)
  modifies a
  requires a.Length > 0
  requires isMaxHeap(a, a.Length - 1)
  ensures multiset(a[..]) == multiset(old(a[..]))
  ensures sorted(a, 0, a.Length)



method {:verify true} HeapSort(a: array<int>)
  modifies a
  requires a.Length > 0
  ensures multiset(a[..]) == multiset(old(a[..]))
  ensures sorted(a, 0, a.Length)
{
  if a.Length < 2 { return; }
  Heapify(a);
  UnHeapify(a);
}