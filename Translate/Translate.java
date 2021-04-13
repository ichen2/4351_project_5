package Translate;
import Symbol.Symbol;
import Tree.BINOP;
import Tree.CJUMP;
import Temp.Temp;
import Temp.Label;

public class Translate {
  public Frame.Frame frame;
  public Translate(Frame.Frame f) {
    frame = f;
  }
  private Frag frags;
  public void procEntryExit(Level level, Exp body) {
    Frame.Frame myframe = level.frame;
    Tree.Exp bodyExp = body.unEx();
    Tree.Stm bodyStm;
    if (bodyExp != null)
      bodyStm = MOVE(TEMP(myframe.RV()), bodyExp);
    else
      bodyStm = body.unNx();
    ProcFrag frag = new ProcFrag(myframe.procEntryExit1(bodyStm), myframe);
    frag.next = frags;
    frags = frag;
  }
  public Frag getResult() {
    return frags;
  }

  private static Tree.Exp CONST(int value) {
    return new Tree.CONST(value);
  }
  private static Tree.Exp NAME(Label label) {
    return new Tree.NAME(label);
  }
  private static Tree.Exp TEMP(Temp temp) {
    return new Tree.TEMP(temp);
  }
  private static Tree.Exp BINOP(int binop, Tree.Exp left, Tree.Exp right) {
    return new Tree.BINOP(binop, left, right);
  }
  private static Tree.Exp MEM(Tree.Exp exp) {
    return new Tree.MEM(exp);
  }
  private static Tree.Exp CALL(Tree.Exp func, Tree.ExpList args) {
    return new Tree.CALL(func, args);
  }
  private static Tree.Exp ESEQ(Tree.Stm stm, Tree.Exp exp) {
    if (stm == null)
      return exp;
    return new Tree.ESEQ(stm, exp);
  }

  private static Tree.Stm MOVE(Tree.Exp dst, Tree.Exp src) {
    return new Tree.MOVE(dst, src);
  }
  private static Tree.Stm UEXP(Tree.Exp exp) {  
    return new Tree.UEXP(exp);
  }
  private static Tree.Stm JUMP(Label target) {
    return new Tree.JUMP(target);
  }
  private static
  Tree.Stm CJUMP(int relop, Tree.Exp l, Tree.Exp r, Label t, Label f) {
    return new Tree.CJUMP(relop, l, r, t, f);
  }
  private static Tree.Stm SEQ(Tree.Stm left, Tree.Stm right) {
    if (left == null)
      return right;
    if (right == null)
      return left;
    return new Tree.SEQ(left, right);
  }
  private static Tree.Stm LABEL(Label label) {
    return new Tree.LABEL(label);
  }

  private static Tree.ExpList ExpList(Tree.Exp head, Tree.ExpList tail) {
    return new Tree.ExpList(head, tail);
  }
  private static Tree.ExpList ExpList(Tree.Exp head) {
    return ExpList(head, null);
  }
  private static Tree.ExpList ExpList(ExpList exp) {
    if (exp == null)
      return null;
    return ExpList(exp.head.unEx(), ExpList(exp.tail));
  }

  public Exp Error() {
    return new Ex(CONST(0));
  }

  public Exp SimpleVar(Access access, Level level) {
    Level lvl = level;
    Tree.Exp framePointer = TEMP(level.frame.FP());
    while(lvl != access.home) {
      framePointer = lvl.formals.head.acc.exp(framePointer);
      lvl = lvl.parent;
    }
    return new Ex(access.acc.exp(framePointer));
  }

  public Exp FieldVar(Exp record, int index) {
    Temp register = new Temp();
    int offset = index * frame.wordSize();
    Tree.Stm stm = MOVE(TEMP(register), record.unEx());
    Tree.Exp exp = MEM(BINOP(Tree.BINOP.PLUS, TEMP(register), CONST(offset)));
    return new Ex(ESEQ(stm, exp));
  }

  public Exp SubscriptVar(Exp array, Exp index) {
    Temp register = new Temp();
    Tree.Exp offset = BINOP(Tree.BINOP.MUL, index.unEx(), CONST(frame.wordSize()));
    Tree.Stm stm = MOVE(TEMP(register), array.unEx());
    Tree.Exp exp = MEM(BINOP(Tree.BINOP.PLUS, TEMP(register), offset));
    return new Ex(ESEQ(stm, exp));
  }

  public Exp NilExp() {
    return new Ex(CONST(0));
  }

  public Exp IntExp(int value) {
    return new Ex(CONST(value));
  }

  private java.util.Hashtable strings = new java.util.Hashtable();
  public Exp StringExp(String lit) {
    String u = lit.intern();
    Label lab = (Label)strings.get(u);
    if (lab == null) {
      lab = new Label();
      strings.put(u, lab);
      DataFrag frag = new DataFrag(frame.string(lab, u));
      frag.next = frags;
      frags = frag;
    }
    return new Ex(NAME(lab));
  }

  private Tree.Exp CallExp(Symbol f, ExpList args, Level from) {
    return frame.externalCall(f.toString(), ExpList(args));
  }
  private Tree.Exp CallExp(Level f, ExpList args, Level from) {
    Tree.Exp fp = TEMP(from.frame.FP());
    Level lvl = from;
    while(lvl != f.parent) {
      fp = lvl.frame.formals.head.exp(fp);
      lvl = lvl.parent;
    }
    Tree.Exp fun = NAME(f.frame.name);
    Tree.ExpList pointerArgs = ExpList(fp, ExpList(args));
    return CALL(fun, pointerArgs);
  }

  public Exp FunExp(Symbol f, ExpList args, Level from) {
    return new Ex(CallExp(f, args, from));
  }
  public Exp FunExp(Level f, ExpList args, Level from) {
    return new Ex(CallExp(f, args, from));
  }
  public Exp ProcExp(Symbol f, ExpList args, Level from) {
    return new Nx(UEXP(CallExp(f, args, from)));
  }
  public Exp ProcExp(Level f, ExpList args, Level from) {
    return new Nx(UEXP(CallExp(f, args, from)));
  }

  public Exp OpExp(int op, Exp left, Exp right) {
    return new Ex(BINOP(op, left.unEx(), right.unEx()));   
  }

  public Exp StrOpExp(int op, Exp left, Exp right) {
    return new RelCx(op, left.unEx(), right.unEx());
  }

  public Exp RecordExp(ExpList init) {
    int count = 0;
    ExpList field = init;
    while(field != null) {
      count++;
      field = field.tail;
    }
    Temp location = new Temp();
    Tree.Stm recordStm = MOVE(TEMP(location), frame.externalCall("allocRecord", ExpList(CONST(count))));
    Tree.Stm fieldStm = recordFields(init, location, 0);
    return new Ex(ESEQ(SEQ(recordStm, fieldStm), TEMP(location)));
  }

  Tree.Stm recordFields(ExpList field, Temp initialLocation, int offset) {
    // Calculate the heads location
    Tree.Stm moveCurrentFieldStm = MOVE(MEM(BINOP(Tree.BINOP.PLUS, TEMP(initialLocation), CONST(offset))), field.head.unEx());
    
    if (field.head == null) {
      // If the head is null, there is a problem, just give a null
      return null;
    } else if (field.tail == null) {
      // If the tail is null, just the move sequence
      return moveCurrentFieldStm;
    } else {
      // If both are present, return a new list recusively
      Tree.Stm nextField = recordFields(field.tail, initialLocation, offset + frame.wordSize());
      
      return SEQ(moveCurrentFieldStm, nextField);
    }
  }

  public Exp SeqExp(ExpList e) {
    Nx exp = null;
    if (e != null)
      exp = new Nx(null);
    while (e != null) {
      if (e.head != null)
        exp = new Nx(SEQ(e.head.unNx(), exp.unNx()));
      e = e.tail;
    }
    return exp;
  }

  public Exp AssignExp(Exp lhs, Exp rhs) {
    return new Nx(MOVE(lhs.unEx(), rhs.unEx()));
  }

  public Exp IfExp(Exp cc, Exp aa, Exp bb) {
    return new IfThenElseExp(cc, aa, bb);
  }

  public Exp WhileExp(Exp test, Exp body, Label done) {
    Label testLabel = new Label();
    Label top = new Label();
    return new Nx(new Tree.SEQ(new Tree.JUMP(testLabel),
      new Tree.SEQ(new Tree.LABEL(top),
        new Tree.SEQ(body.unNx(),
          new Tree.SEQ(new Tree.LABEL(testLabel),
            new Tree.SEQ(test.unCx(top, done),
              new Tree.LABEL(done)))))));
  }

  public Exp ForExp(Access i, Exp lo, Exp hi, Exp body, Label done) {
    Access limit = i;
    Level d = i.home;
    return (new Nx(SEQ(AssignExp(SimpleVar(i, d), lo).unNx(), AssignExp(
        SimpleVar(limit, d), hi).unNx())));
  }

  public Exp BreakExp(Label done) {
    return new Nx(JUMP(done));
  }

  public Exp LetExp(ExpList lets, Exp body) {
    ExpList temp = null;
    ExpList iter = lets;
    Exp exp = body;
    
    if (iter != null) {
      return new Ex(ESEQ(iter.head.unNx(), body.unEx()));
    } else {
      return new Nx(SEQ(lets.head.unNx(), body.unNx()));
    }
  }

  public Exp ArrayExp(Exp size, Exp init) {
    Label initArray = new Label("initArray");
    return new Ex(new Tree.CALL(NAME(initArray), new Tree.ExpList(size
        .unEx(), new Tree.ExpList(init.unEx(), null))));
  }

  public Exp VarDec(Access a, Exp init) {
    return new Nx(MOVE(a.acc.exp(TEMP(a.home.frame.FP())), init.unEx()));
  }

  public Exp TypeDec() {
    return new Nx(null);
  }

  public Exp FunctionDec() {
    return new Nx(null);
  }
}
