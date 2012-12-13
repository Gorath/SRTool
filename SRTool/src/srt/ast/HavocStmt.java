package srt.ast;

import java.util.ArrayList;

public class HavocStmt extends Stmt {
	
	public HavocStmt(DeclRef variable) {
		this(variable, null);
	}
	
	public HavocStmt(DeclRef variable, Node basedOn)
	{
		super(basedOn);
		children.add(variable);
	}
	
	public DeclRef getVariable() {
		return (DeclRef) children.get(0);
	}

    @Override
    public ArrayList<Node> getModSet() {
        ArrayList<Node> modSet = new ArrayList<Node>();
        modSet.add(this.getVariable());
        return modSet;
    }
}
