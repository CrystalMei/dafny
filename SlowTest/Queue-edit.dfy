// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Queue.dfy
// Dafny version of Queue.bpl
// Rustan Leino, 2008

datatype Option<T> = None | Some(v:T) 
datatype Node<T> = Node(data: T, next: Option<Node<T>>, tailContents: seq<T>)

predicate NodeValid(n: Node)
{
    (n.next == None ==> n.tailContents == []) &&
    (n.next != None ==> n.tailContents == [n.next.v.data] + n.next.v.tailContents)
}

function method NodeInit(): (n: Node)
    ensures NodeValid(n)
    ensures n.next == None
{ Node(_, None, [])} // how to initialize a datatype without all initial values?

datatype Queue<T> = Queue(head: Node<T>, tail: Node<T>, contents: seq<T>, spine: set<Node<T>>)

predicate QueueValid(q: Queue)
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

function method QueueInit(): (q: Queue)
    ensures QueueValid(q)
    ensures |q.contents| == 0
{
    var n := NodeInit();
    Queue(n, n, n.tailContents, {n})
}

// method Enqueue<T> (q: Queue, t: T) returns (q': Queue)
//     requires QueueValid(q)
//     ensures ValQueueValidid(q')
//     ensures q'.contents == q.contents + [t]
// {
//     var n := NodeInit();
//     n.data := t;
//     tail.next := n;
//     tail := n;

//     forall m | m in spine {
//       m.tailContents := m.tailContents + [t];
//     }
//     contents := head.tailContents;

//     forall m | m in spine {
//       m.footprint := m.footprint + n.footprint;
//     }
//     footprint := footprint + n.footprint;

//     spine := spine + {n};

// }
