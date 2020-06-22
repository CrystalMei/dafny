// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Option<T> = None | Some(v:T) 
datatype Node = Node(Contents: set<int>, data: int, left: Option<Node>, right: Option<Node>)
datatype IntSet = IntSet(Contents: set<int>, root: Option<Node>)

predicate ISValid(is:IntSet)
{
  (is.root == None ==> is.Contents == {}) &&
  (is.root != None ==>
      NodeValid(is.root.v) && is.Contents == is.root.v.Contents)
}

function method ISInit(): (is:IntSet)
  ensures ISValid(is)
  ensures is.Contents == {}
{ IntSet({}, None) }

function method ISFind(is: IntSet, x: int): bool
  requires ISValid(is)
  ensures ISFind(is, x) <==> x in is.Contents
{ is.root != None && NodeFind(is.root.v, x) }

method Insert (is: IntSet, x: int) returns (is': IntSet)
    requires ISValid(is)
    ensures ISValid(is')
    ensures is'.Contents == is.Contents + {x}
{
  var t := InsertHelper(x, is.root);
  is' := IntSet(t.Contents, Some (t));
}

method InsertHelper(x: int, n: Option<Node>) returns (m: Node)
    requires n == None || NodeValid(n.v)
    ensures NodeValid(m)
    ensures n == None ==> m.Contents == {x}
    ensures n != None ==> m.Contents == n.v.Contents + {x}
    decreases x, n
{
  if n == None {      
    m := NodeInit(x);
  } else if x == n.v.data {
      m := n.v;
  } else {
    m := n.v;
    if x < n.v.data {
      assert n.v.right == None || NodeValid(n.v.right.v);
      var t := InsertHelper(x, n.v.left);
      m := Node(m.Contents, m.data, Some(t), m.right);
    } else {
      assert n.v.left == None || NodeValid(n.v.left.v);
      var t := InsertHelper(x, n.v.right);
      m := Node(m.Contents, m.data, m.left, Some(t));
    }
    m := Node(m.Contents + {x}, m.data, m.left, m.right);
  }
}

method ISRemove (is: IntSet, x: int) returns (is': IntSet)
    requires ISValid(is)
    ensures ISValid(is')
    ensures is'.Contents == is.Contents - {x}
{
  is' := is;
  if is.root != None {
    var newRoot := NodeRemove(is.root.v, x);
    is' := IntSet(is'.Contents, newRoot);
    if is'.root == None {
      is' := IntSet({}, None);
    } else {
      is' := IntSet(is'.root.v.Contents, is'.root);
    }
  }
}

predicate NodeValid(n:Node)
  decreases n
{
  (n.left != None ==> 
    NodeValid(n.left.v) && 
    (forall y :: y in n.left.v.Contents ==> y < n.data)) &&
  (n.right != None ==> 
    NodeValid(n.right.v) && 
    (forall y :: y in n.right.v.Contents ==> n.data < y)) &&
  (n.left == None && n.right == None ==>
    n.Contents == {n.data}) &&
  (n.left != None && n.right == None ==>
    n.Contents == n.left.v.Contents + {n.data}) &&
  (n.left == None && n.right != None ==>
    n.Contents == {n.data} + n.right.v.Contents) &&
  (n.left != None && n.right != None ==>
    n.Contents == n.left.v.Contents + {n.data} + n.right.v.Contents)    
}

function method NodeInit(x: int): (n: Node)
  ensures NodeValid(n)
  ensures n.Contents == {x}
{ Node({x}, x, None, None) }

function method NodeFind(n: Node, x: int): bool
    requires NodeValid(n)
    ensures NodeFind(n, x) <==> x in n.Contents
    decreases n
{
  if x == n.data then
    true
  else if n.left != None && x < n.data then
    NodeFind(n.left.v, x)
  else if n.right != None && n.data < x then
    NodeFind(n.right.v, x)
  else
    false
}

method NodeRemove (n: Node, x: int) returns (n': Option<Node>)
    requires NodeValid(n)
    ensures n' != None ==> NodeValid(n'.v)
    ensures n' == None ==> n.Contents <= {x}
    ensures n' != None ==> n'.v.Contents == n.Contents - {x}
    decreases n
{
  if(*) {
    n' := Some (n);
    if n.left != None && x < n.data {
      var t := NodeRemove(n.left.v, x);
      n' := Some (Node(n.Contents - {x}, n.data, t, n.right));
    } else if n.right != None && n.data < x {
      var t := NodeRemove(n.right.v, x);
      n' := Some (Node(n.Contents - {x}, n.data, n.left, t));
    } else if x == n.data {
      if n.left == None && n.right == None {
        n' := None;
      } else if n.left == None {
        n' := n.right;
      } else if n.right == None {
        n' := n.left;
      } else {
        // rotate
        var min, r := RemoveMin(n.right.v);
        n' := Some (Node(n.Contents - {x}, min, n.left, r));
      }
    }
  } else {
    n' := Some (n);
    if n.left != None && x < n.data {
      var t := NodeRemove(n.left.v, x);
      n' := Some (Node(n.Contents - {x}, n.data, t, n.right));
    } else if n.right != None && n.data < x {
      var t := NodeRemove(n.right.v, x);
      n' := Some (Node(n.Contents - {x}, n.data, n.left, t));
    } else if x == n.data {
      if n.left == None && n.right == None {
        n' := None;
      } else if n.left == None {
        n' := n.right;
      } else if n.right == None {
        n' := n.left;
      } else {
        // rotate
        var min, r := RemoveMin(n.right.v);
        n' := Some (Node(n.Contents - {x}, min, n.left, r));
      }
    }
  }
}

method RemoveMin (n: Node) returns (min: int, n': Option<Node>)
  requires NodeValid(n)
  ensures n' != None ==> NodeValid(n'.v)
  ensures n' == None ==> n.Contents == {min}
  ensures n' != None ==> n'.v.Contents == n.Contents - {min}
  ensures min in n.Contents && (forall x :: x in n.Contents ==> min <= x)
  decreases n
{
  if n.left == None {
    min := n.data;
    n' := n.right;
  } else {
    var t;
    min, t := RemoveMin(n.left.v);
    n' := Some (Node(n.Contents - {min}, n.data, t, n.right));
  }
}

method Client0(x: int)
{
  var s := ISInit();

  s := Insert(s, 12);
  s := Insert(s, 24);
  var present := ISFind(s, x);
  assert present <==> x == 12 || x == 24;
}

method Client1(s: IntSet, x: int)
  requires ISValid(s)
{
  var s' := Insert(s, x);
  s' := Insert(s', 24);
  assert s.Contents - {x,24} == s'.Contents - {x,24};
}