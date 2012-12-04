package srt.tool;

import java.util.HashMap;
import java.util.Map;

import srt.ast.AssignStmt;
import srt.ast.Decl;
import srt.ast.DeclRef;
import srt.ast.Expr;
import srt.ast.visitor.impl.DefaultVisitor;

public class SSAVisitor extends DefaultVisitor {
    private Map<String, Integer> index = new HashMap<String, Integer>();

    public SSAVisitor() {
        super(true);
    }

    private String getSSAName(String name) {
        int i = index.get(name);
        return name + "$" + i;
    }

    private void incrementSSAIndex(String name) {
        int i = index.get(name) + 1;
        index.put(name, i);
    }

    @Override
    public Object visit(Decl decl) {
        index.put(decl.getName(), 0);
        String ssaName = getSSAName(decl.getName());
        return new Decl(ssaName, decl.getType(), decl);
    }

    @Override
    public Object visit(DeclRef declRef) {
        String ssaName = getSSAName(declRef.getName());
        return super.visit(new DeclRef(ssaName, declRef));
    }

    @Override
    public Object visit(AssignStmt assignment) {
        Expr expr = (Expr) super.visit(assignment.getRhs());
        String name = assignment.getLhs().getName();
        incrementSSAIndex(name);
        DeclRef declRef = (DeclRef) visit(assignment.getLhs());
        return new AssignStmt(declRef, expr, assignment);
    }
}
