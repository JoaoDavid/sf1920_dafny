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
        (first == last) <==> (n == 0 || n == q.Length) &&
        (n > 0 && first < last) ==> (n == last - first) &&
        (n > 0 && first >= last) ==> (n == (q.Length + last - first))
 
    }

    constructor (length : nat)
        requires length > 0
        ensures q.Length > 0
        //ensures contents == []
    {
        q := new T[length];
        n := 0;
        first := 0;
        last := 0;
        //contents := []; // ghost code
    }

    function method IsEmpty(): bool
        //ensures IsEmpty() <==> contents == []
        ensures IsEmpty() ==> first == last
    {
        n == 0
    }

    
    function method IsFull(): bool
        ensures IsFull() <==> n == q.Length
        //ensures !IsFull() ==> last > 0
    {
        n == q.Length
    }

    // Adds the item to this queue 
    method Enqueue(item: T)
        requires !IsFull()
    {  
        assert n != q.Length;
    }

    // Removes and returns the item on this queue that was least recently added 
    method Dequeue() returns (item: T)
        requires !IsEmpty()
    {
        assert n > 0;
        if (first < last){
            assert n == last - first;
            first := first + 1;
            n := n - 1;
        } else {
            assert n > 0 && first >= last;
            assert n == (q.Length + last - first);
        }
    }

    // Returns the item least recently added to this queue 
    function method Peek(): T
        requires !IsEmpty()
        //ensures contents == old(contents)
    {   
        q[first]
    }

}