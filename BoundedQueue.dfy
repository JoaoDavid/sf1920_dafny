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
        q.Length > 0 &&
        //contents == q[0..n] &&
        (first == last) <==> (n == 0 || n == q.Length) &&
        (n > 0 && first < last) ==> n == last - first &&
        (n > 0 && first >= last) ==> n == q.Length + last - first
        /*first < last ==> contents == q[first..last] &&
        first > last ==> contents == q[0..last] + q[first..q.Length] && 
        n == q.Length ==> contents == q[0..n] &&
        n == 0 <==> contents == []*/
        
    }

    constructor (length : nat)
        requires length > 0
        ensures Valid()
    {
        q := new T[length];
        n := 0;
        first := 0;
        last := 0;
        //contents := q[0..n]; // ghost code
    }

    function method IsEmpty(): bool
    {
        n == 0
    }

    
    function method IsFull(): bool
        //ensures IsFull() <==> n == q.Length
        //ensures !IsFull() ==> last > 0
    {
        n == q.Length
    }

    // Adds the item to this queue 
    method Enqueue(item: T)
        requires !IsFull()
    {   
        /*if (last < first) {
            q[last] := item;
            last := last + 1;
            n := n + 1;
            assert Valid();
            //contents := q[0..n];
        } else if(first == last) { //vai dar a volta
               q[last] := item;
               n := n + 1;
               last := 0;
               assert Valid();
          
          
        }*/
        if (last < q.Length - 1 && n == 0) {
            q[last] := item;
            last := last + 1;
            n := last - first;
            assert last < q.Length;
            assert Valid();
        }
    }

    // Removes and returns the item on this queue that was least recently added 
    method Dequeue() returns (item: T)
        requires !IsEmpty()
    {
        
    }

    // Returns the item least recently added to this queue 
    function method Peek(): T
        requires !IsEmpty()
    {   
        q[first]
    }



}
