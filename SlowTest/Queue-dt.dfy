// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Queue.dfy
// Dafny version of Queue.bpl
// Rustan Leino, 2008

datatype Option<T> = None | Some(v:T)

datatype Node<T(0)> = Node(data: T, next: Option<Node<T>>, tailContents: seq<T>)

predicate NodeValid(n: Node)
{
    (n.next == None ==> n.tailContents == []) &&
    (n.next != None ==> n.tailContents == [n.next.v.data] + n.next.v.tailContents)
}

function method NodeInit<T(0)>(): (n: Node)
    ensures NodeValid(n)
    ensures n.next == None
{   var t: T :| true;
    Node(t, None, [])
}

function method NodeInitData<T(0)>(d: T): (n: Node)
    ensures NodeValid(n)
    ensures n.next == None
{ Node(d, None, [])}

datatype Queue<T(0)(==)> = Queue(head: Node<T>, tail: Node<T>, contents: seq<T>, spine: set<Node<T>>)

predicate QueueValid<T(0)>(q: Queue)
{   
    q.head in q.spine &&
    q.tail in q.spine &&
    q.tail.next == None &&
    (forall n ::
        n in q.spine ==>
        NodeValid(n) &&
        (n.next == None ==> n == q.tail) ) &&
    (forall n ::
        n in q.spine ==>
        n.next != None ==> n.next.v in q.spine) &&
    q.contents == q.head.tailContents
}

function method QueueInit<T(0)(==)>(): (q: Queue)
    ensures QueueValid(q)
    ensures |q.contents| == 0
{
    var n := NodeInit();
    Queue(n, n, n.tailContents, {n})
}

method IsEmpty<T(0)(==)>(q: Queue) returns (isEmpty: bool)
  requires QueueValid(q)
  ensures isEmpty <==> |q.contents| == 0
{
  isEmpty := q.head == q.tail;
}

// problem: should update spine about old tail
method Enqueue<T(0)(==)>(q: Queue, t: T) returns (q': Queue)
    requires QueueValid(q)
    ensures QueueValid(q')
    ensures q'.contents == q.contents + [t]
{
    var n := NodeInitData(t);
    var tail' := n;
    q' := Queue(q.head, tail', q.contents, q.spine);

    var spine' := set x: Node<T> | x in q'.spine :: Node(x.data, x.next, x.tailContents + [t]);
    var head' := Node(q'.head.data, q'.head.next, q'.head.tailContents + [t]);
    var content' := head'.tailContents;
    q' := Queue(head', q'.tail, content', spine' + {n});
}

method Front<T(0)(==)>(q: Queue) returns (t: T)
  requires QueueValid(q)
  requires 0 < |q.contents|
  ensures t == q.contents[0]
{
  t := q.head.next.v.data;
}

method Dequeue<T(0)(==)>(q: Queue) returns (q': Queue)
  requires QueueValid(q)
  requires 0 < |q.contents|
  ensures QueueValid(q')
  ensures q'.contents == (q.contents)[1..]
{
  var n := q.head.next;
  q' := Queue(n.v, q.tail, n.v.tailContents, q.spine);
}

method Rotate<T(0)(==)>(q: Queue) returns (q': Queue)
  requires QueueValid(q)
  requires 0 < |q.contents|
  ensures QueueValid(q')
  ensures q'.contents == (q.contents)[1..] + (q.contents)[..1]
{
  var t := Front(q);
  q' := Dequeue(q);
  q' := Enqueue(q', t);
}

method RotateAny<T(0)(==)>(q: Queue) returns (q': Queue)
  requires QueueValid(q)
  requires 0 < |q.contents|
  ensures QueueValid(q')
  ensures |q'.contents| == |q.contents|
  ensures exists i :: 0 <= i && i <= |q.contents| &&
            q'.contents == (q.contents)[i..] + (q.contents)[..i]
{
  var t := Front(q);
  q':= Dequeue(q);
  q' := Enqueue(q', t);
}

class Main<U(0)(==)> {
  method A<T(0)(==)>(t: T, u: T, v: T)
  {
    var q0 := QueueInit();
    var q1 := QueueInit();

    q0 := Enqueue(q0, t);
    q0 := Enqueue(q0, u);

    q1 := Enqueue(q1, v);

    assert |q0.contents| == 2;

    var w := Front(q0);
    assert w == t;
    q0 := Dequeue(q0);

    w := Front(q0);
    assert w == u;

    assert |q0.contents| == 1;
    assert |q1.contents| == 1;
  }

  method Main2<T(0)(==)>(t: U, u: U, v: U, q0: Queue<U>, q1: Queue<U>)
    requires QueueValid(q0)
    requires QueueValid(q1)
    requires |q0.contents| == 0
  {
    var q0' := Enqueue(q0, t);
    q0' := Enqueue(q0', u);

    var q1' := Enqueue(q1, v);

    assert |q0'.contents| == 2;

    var w := Front(q0');
    assert w == t;
    q0' := Dequeue(q0');

    w := Front(q0');
    assert w == u;

    assert |q0'.contents| == 1;
    assert |q1'.contents| == |q1.contents| + 1;
  }
}
