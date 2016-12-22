package graphdbInt;
import java.util.ArrayList;


public class clause {
	
	public ArrayList<String> preds;
	public double wt;

	public clause()
	{
		this.preds = new ArrayList<String>();
		this.wt = 0;
	}
}
