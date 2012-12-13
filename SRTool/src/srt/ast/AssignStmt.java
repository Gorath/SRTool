package srt.ast;


import java.util.ArrayList;

public class AssignStmt extends Stmt {
	
	public AssignStmt(DeclRef lhs, Expr rhs) {
		this(lhs, rhs, null);
	}
	
	public AssignStmt(DeclRef lhs, Expr rhs, Node basedOn)
	{
		super(basedOn);
		children.add(lhs);
		children.add(rhs);
	}

	public DeclRef getLhs() {
		return (DeclRef) children.get(0);
	}
	
	public Expr getRhs() {
		return (Expr) children.get(1);
	}

    @Override
    public ArrayList<Node> getModSet() {
        ArrayList<Node> modSet = new ArrayList<Node>();
        modSet.add(this.getLhs());
        return modSet;
    }

}
