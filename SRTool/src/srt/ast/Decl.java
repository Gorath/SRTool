package srt.ast;

import java.util.ArrayList;
import java.util.List;

public class Decl extends Stmt {
	
	private String name;
	private String type;
	
	public Decl(String name, String type) {
		this(name, type, null);
	}
	
	public Decl(String name, String type, Node basedOn) {
		super(basedOn);
		this.name = name;
		this.type = type;
	}

	public String getName() {
		return name;
	}
	
	public String getType() {
		return type;
	}
//
//    @Override
//    public ArrayList<Node> getModSet() {
//        ArrayList<Node> result =  new ArrayList<Node>();
//        result.add(new DeclRef(this.name));
//        return  result;
//    }
	
}
