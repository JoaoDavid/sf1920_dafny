class {:autocontracts} BoundedQueue<T(0)> {

    ghost var contents: seq<T>
    var q: array<T>
    var n: nat
    var first: nat
    var last: nat

    predicate Valid()
    {
        0 <= n <= q.Length &&
        contents == q[0..n] &&
        0 <= first < q.Length &&
        0 <= last < q.Length &&
        (first == last) <==> (n == 0 || n == q.Length) &&
        (n > 0 && first < last) ==> n == last - first &&
        (n > 0 && first >= last) ==> n == q.Length + last - first
        
    }

    constructor (length : nat)
        requires length > 0
        ensures contents == []
        ensures Valid()
    {
        q := new T[length];
        n := 0;
        first := 0;
        last := 0;
        contents := []; // ghost code
    }

    function method IsEmpty(): bool
        ensures IsEmpty() <==> contents == []
        //ensures IsEmpty() ==> (first == last)
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
        if (first < last) {
            if (last + 1 >= q.Length) {//da a volta
                q[last] := item;
                last := 0;
                n := n + 1;
            } else{
                q[last] := item;
                last := last + 1;
                n := n + 1;
            }
        } else if (first > last) { //first > last
                q[last] := item;
                last := last + 1;
                n := n + 1;
        }
        /*q[last] := item; 
        last := last + 1;*/
    }

    // Removes and returns the item on this queue that was least recently added 
    method Dequeue() returns (item: T)
        requires !IsEmpty()
    {
        /*if(first <= last){
            item := q[first];
            first := first + 1;
            n := n - 1;
        }*/
        //n := n - 1;
        
        /*if (IsFull()) {
            last := q.Length - 1;
            item := q[last];
        } else {
            last := last - 1;
        }
        item := q[last];*/
    }

    // Returns the item least recently added to this queue 
    function method Peek(): T
        requires !IsEmpty()
    {   
        q[first]
    }



}
