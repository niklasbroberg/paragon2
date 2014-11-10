public class Channel
{
  private int id;
  public Channel (int id)
  {
    this.id = id;
  }
  public int get() throws NoBidExc
  {
     System.out.print("Enter bid for bidder "+this.id+": ");
     return Integer.parseInt(System.console().readLine());
  }
  public void put(int winBid)
  {
     System.out.println("Bidder "+id+" receives that the winning bid was "+winBid);
  }
  public void put(java.lang.String data)
  {
     System.out.println("Bidder "+id+" receives data:\n" + data);
  }
}
