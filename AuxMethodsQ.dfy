
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



method Main() {
  print "BoundedQueue\n";
  var length := 3;
  var q := new BoundedQueue<int>(length);
  print "\nPrintQueue "; q.PrintQueue();
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
  //full
  print "\nPrintQueue "; q.PrintQueue();
  if (!q.IsEmpty()){
    var e := q.Dequeue();
    print "\nElemDeq ";print(e);
  }
  if (!q.IsFull()){
    q.Enqueue(-11);
  }
    if (!q.IsEmpty()){
    var e := q.Dequeue();
    print "\nElemDeq ";print(e);
  }
  if (!q.IsFull()){
    q.Enqueue(-11);
  }
  if (!q.IsEmpty()){
    var e := q.Dequeue();
    print "\nElemDeq ";print(e);
  }
  if (!q.IsFull()){
    q.Enqueue(-11);
  }
  
    //pintQueue -11 : -11 : -11 :
    //first: 0  last: 0  n: 3
  
if (!q.IsEmpty()){
    var e := q.Dequeue();
    print "\nElemDeq ";print(e);
  }
  print "\nPrintQueue "; q.PrintQueue();
}
