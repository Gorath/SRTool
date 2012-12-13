package srt.ast;

import java.util.ArrayList;
import java.util.List;

public class StmtList extends Node {
	
	public StmtList(Stmt[] statements) {
		this(statements, null);
	}
	
	public StmtList(Stmt[] statements, Node basedOn) {
		super(basedOn);
		for(Stmt stmt : statements) {
			children.add(stmt);
		}
	}
	
	public StmtList(List<Stmt> statements) {
		this(statements, null);
	}
	
	public StmtList(List<Stmt> statements, Node basedOn) {
		super(basedOn);
		children.addAll(statements);
	}
	
	@SuppressWarnings("unchecked")
	public List<Stmt> getStatements()
	{
		return (List<Stmt>)children.clone();
	}

    @Override
    public ArrayList<Node> getModSet() {
        ArrayList<Node> modSet = new ArrayList<Node>();
        for (Stmt s : this.getStatements()) {
            modSet.addAll(s.getModSet());
        }
        return modSet;
    }
	
}
