/**
 * Reliable Software
 * Department of Informatics
 * Faculty of Sciences
 * University of Lisbon
 * November 18, 2019
 * João David n49448
 *
 * A model-based specification of a bounded queue of elements of type T.
 */
class {:autocontracts} BoundedQueue<T(0)> {

    ghost var contents: seq<T>
    var q: array<T>
    var n: nat
    var first: nat
    var last: nat

    predicate Valid()
    {
        0 <= n <= q.Length &&
        0 <= first < q.Length &&
        0 <= last < q.Length &&
        n == |contents| &&
        ((first == last) <==> (n == 0 || n == q.Length)) &&
        ((n > 0 && first < last) ==> (n == last - first)) &&
        ((n > 0 && first >= last) ==> (n == (q.Length + last - first))) &&
        (contents == if first < last then q[first..last] else if n == 0 then [] else q[first..q.Length] + q[0..last])
    }

    //Initializes an empty queue of length, length
    constructor (length : nat)
        requires length > 0
        ensures contents == []
    {
        q := new T[length];
        n := 0;
        first := 0;
        last := 0;
        contents := [];
    }

    //Is this queue empty? 
    function method IsEmpty(): bool
        ensures IsEmpty() <==> contents == []
    {
        n == 0
    }

    //Is this queue full? 
    function method IsFull(): bool
        ensures IsFull() ==> |contents| == n
    {
        n == q.Length
    }

    // Adds the item to this queue 
    method Enqueue(item: T)
        requires !IsFull()
        ensures contents == old(contents + [item])
    {  
        q[last] := item;
        n := n + 1;
        if (first > last){            
            last := last + 1;
            contents := q[first..q.Length] + q[0..last];
        } else { // first <= last
            if (last + 1 == q.Length){
                last := 0;
                contents := q[first..q.Length];
            } else {
                last := last + 1;
                contents := q[first..last];
            }
        }
    }

    // Removes and returns the item on this queue that was least recently added 
    method Dequeue() returns (item: T)
        requires !IsEmpty()
        ensures contents == old(contents[1..n])
        ensures item == old(contents[0])
    {
        n := n - 1;
        item := q[first];
        if (first < last){            
            first := first + 1;
            contents := q[first..last];
        } else { //first >= last
            if (first + 1 == q.Length){
                first := 0;
                contents := q[first..last];
            } else {
                first := first + 1;
                contents := q[first..q.Length] + q[0..last];
            }
        }
    }

    // Returns the item least recently added to this queue 
    function method Peek(): T
        requires !IsEmpty()
        ensures Peek() == contents[0]
    {   
        q[first]
    }

}
