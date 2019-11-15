class {:autocontracts} BoundedQueue<T(0)> {

    ghost var contents: seq<T>
    var q: array<T>
    var n: nat
    var first: nat
    var last: nat

    predicate Valid()
        reads this,q
    {
        0 <= n <= q.Length &&
        0 <= first < q.Length &&
        0 <= last < q.Length &&
        q.Length > 0 &&
        ((first == last) <==> (n == 0 || n == q.Length)) &&
        ((n > 0 && first < last) ==> (n == last - first)) &&
        ((n > 0 && first >= last) ==> (n == (q.Length + last - first)))
         //&&
        //(n == 0 && first == last) ==> (n == (last - first) || n == first - last)
 
    }

    constructor (length : nat)
        requires length > 0
        ensures Valid()
        //ensures contents == []
    {
        q := new T[length];
        n := 0;
        first := 0;
        last := 0;
        //contents := []; // ghost code
    }

    function method IsEmpty(): bool
        //reads this,q
        requires Valid()
        ensures Valid()
        //ensures IsEmpty() <==> contents == []
        //ensures IsEmpty() ==> first == last
    {
        n == 0
    }

    
    function method IsFull(): bool
        //reads this,q
        requires Valid()
        ensures Valid()
        ensures IsFull() <==> n == q.Length
        //ensures !IsFull() ==> last > 0
    {
        n == q.Length
    }

    // Adds the item to this queue 
    method Enqueue(item: T)
        modifies this,q
        requires Valid()
        ensures Valid()
        requires !IsFull()
        ensures q == old(q)
        /*ensures n < q.Length ==> !IsFull()
        ensures n == q.Length ==> IsFull()*/
    {  
        q[last] := item;
        assert n != q.Length;
        if (first > last){            
            last := last + 1;
            n := n + 1;
            assert Valid();
        } else if (first < last) {
            if (last + 1 == q.Length){
                last := 0;
                n := n + 1;
            } else {
                last := last + 1;
                n := n + 1;
            }
        } else if (IsEmpty()){ //first == last
                assert n == 0;
                assert first == last;
                //n := n + 1;
            if (last + 1 == q.Length ){//&& first + 1 == q.Length) {
                last := 0;
                n := n + 1;
                assert n != 0;
               //assert last < first;
                //assert n != q.Length;
                
                //n := q.Length + last - first    
            } else {//first enqueue after new object
                last := last + 1;
                n := n + 1;
            }
        }
    }

    // Removes and returns the item on this queue that was least recently added 
    method Dequeue() returns (item: T)
        requires Valid()
        ensures Valid()
        requires !IsEmpty()
    {
        assert n > 0;
        item := q[first];
        if (first < last){            
            first := first + 1;
            n := n - 1;
            assert Valid();
        } else if (first > last) {
            if (first + 1 == q.Length){
                first := 0;
                n := n - 1;
            } else {
                first := first + 1;
                n := n - 1;
            }
        } else if (IsFull()){ //first == last
                assert n == q.Length;
                assert first == last;
                //n := n + 1;
            if (first + 1 == q.Length ){//&& first + 1 == q.Length) {
                first := 0;
                n := n - 1;   
            } else {//first enqueue after new object
                first := first + 1;
                n := n - 1;
            }
        }
    }

    // Returns the item least recently added to this queue 
    function method Peek(): T
        //reads this,q
        requires Valid()
        ensures Valid()
        requires !IsEmpty()
        //ensures contents == old(contents)
    {   
        assert  0 <= first ;
        q[first]
    }

    function method Size(): nat
        //reads this,q
        requires Valid()
        ensures Valid()
        //ensures contents == old(contents)
    {   
        n
    }

    method PrintQueue()
        //reads this,q
        requires Valid()
        ensures Valid()
        //ensures contents == old(contents)
    {   
        var i := 0;
        while(i < q.Length) {
            print q[i];
            print " : ";
            i := i + 1;
        }
        print "\n";
        print "first: "; print first;
        print "  last: "; print last;
        print "  n: "; print n;
    }

}

method Main() {
  print "BoundedQueue\n";
  var length := 3;
  var q := new BoundedQueue<int>(length);
  //---------------------
  if (!q.IsFull()){
    q.Enqueue(-1);
  }
  if (!q.IsFull()){
    q.Enqueue(-2);
  }
  if (!q.IsFull()){
    q.Enqueue(-3);
  }
  if (!q.IsFull()){
    q.Enqueue(-4);
  }
  if (!q.IsEmpty()){
    var e := q.Dequeue();
    print "\nElemDeq ";print(e);
  }
  if (!q.IsFull()){
    q.Enqueue(-4);
  }
  print "\nPrintQueue "; q.PrintQueue();
  if (!q.IsEmpty()){
    var e := q.Dequeue();
    print "\nElemDeq ";print(e);
  }
  if (!q.IsEmpty()){
    var e := q.Dequeue();
    print "\nElemDeq ";print(e);
  }
  print "\nPrintQueue "; q.PrintQueue();
}
