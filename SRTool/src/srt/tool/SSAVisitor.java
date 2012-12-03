package srt.tool;

import java.util.HashMap;
import java.util.Map;

import srt.ast.AssignStmt;
import srt.ast.Decl;
import srt.ast.DeclRef;
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
        if (index.get(name) == null){
            index.put(name, 0);
        } else {
            int i = index.get(name) + 1;
            index.put(name, i);
        }
    }

    @Override
    public Object visit(Decl decl) {
        return super.visit(decl);
    }

    @Override
    public Object visit(DeclRef declRef) {
        return super.visit(new DeclRef(getSSAName(declRef.getName())));
    }

    @Override
    public Object visit(AssignStmt assignment) {
        String name = assignment.getLhs().getName();
        incrementSSAIndex(name);
        String ssaName = getSSAName(name);
        return super.visit(new AssignStmt(new DeclRef(ssaName), assignment.getRhs()));
    }
}
