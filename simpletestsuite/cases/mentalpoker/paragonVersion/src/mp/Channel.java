package mp;
import java.io.*;
public class Channel
{
  public final static se.chalmers.paragon.ConcreteActor channel = se.chalmers.paragon.Actor.newConcreteActor("channel");
  public final static se.chalmers.paragon.Policy channelP = se.chalmers.paragon.Policy.newPolicy("channelP", se.chalmers.paragon.Policy.newPClause(channel));
  public static final java.io.PrintStream out = System.out;
  public static final java.io.InputStream in = System.in;
}