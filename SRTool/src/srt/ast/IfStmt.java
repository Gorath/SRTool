package srt.ast;

import java.util.ArrayList;

public class IfStmt extends Stmt {
	
	public IfStmt(Expr condition, Stmt thenStmt, Stmt elseStmt) {
		this(condition, thenStmt, elseStmt, null);
	}
	public IfStmt(Expr condition, Stmt thenStmt, Stmt elseStmt, Node basedOn) {
		super(basedOn);
		children.add(condition);
		children.add(thenStmt);
		children.add(elseStmt);
	}
	
	public Expr getCondition()
	{
		return (Expr) children.get(0);
	}
	
	public Stmt getThenStmt()
	{
		return (Stmt) children.get(1);
	}
	
	/**
	 * This can be null.
	 * But {@code srt.ast.visitor.impl.MakeBlockVisitor}
	 * ensures it is never null.
	 * @return
	 */
	public Stmt getElseStmt()
	{
		return (Stmt) children.get(2);
	}

    @Override
    public ArrayList<Node> getModSet() {
        ArrayList<Node> modSet = new ArrayList<Node>();
        modSet.addAll(this.getThenStmt().getModSet());
        modSet.addAll(this.getElseStmt().getModSet());
        return modSet;
    }

}
