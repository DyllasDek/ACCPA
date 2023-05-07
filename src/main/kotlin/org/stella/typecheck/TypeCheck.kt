package org.stella.typecheck


import org.stella.TypeErrorOut
import org.syntax.stella.Absyn.*
import java.util.*

object TypeCheck {
    private var out: TypeErrorOut = TypeErrorOut()
    private var identTypes: LinkedHashMap<String, Type> = LinkedHashMap()

    @Throws(Exception::class)
    fun typecheckProgram(program: Program) {
        when (program) {
            is AProgram -> program.listdecl_.map {
                when (it) {
                    is DeclFun -> {
                        visitDeclFn(it, LinkedHashMap(identTypes))
                    }
                }
            }

        }
    }

    /**
     * Visit declaration of fn and add it to type table
     * @param fn Function to visit
     * @param iTable Type table
     */
    private fun visitDeclFn(fn: DeclFun, iTable: LinkedHashMap<String, Type>) {
        // Remember name of fn
        val name = fn.stellaident_
        // Add all params to Type Table at current scope
        val inTypes = ListType()
        fn.listparamdecl_.forEach {
            when(it) {
                is AParamDecl -> {
                    iTable[it.stellaident_] = it.type_
                    inTypes.add(it.type_)
                }
            }
        }
        // Evaluate expression and get its type
        var actualType : Type = TypeNat()
        if (fn.returntype_ is SomeReturnType) {
            actualType = visitExpr(fn.expr_, LinkedHashMap(iTable), fn.returntype_.type_)
        } else {
        }
        // Compare actual type with declared type
        when(val returnType = fn.returntype_) {
            is SomeReturnType -> {
                if (returnType.type_ != actualType) {
                    // Report error
                    out.expected_got(returnType.type_,actualType,fn.stellaident_)
                }
            }
        }

        identTypes[name] = TypeFun(inTypes,actualType)
    }

    /**
     * Visit expression
     * @param expr Expression to visit
     * @param iTable Type table
     * @return Type of expression
     */
    private fun visitExpr(expr: Expr, iTable: LinkedHashMap<String, Type>, expType: Type): Type {
        // "Type" match
        when (expr) {
            // If Const Integer, then it is Nat
            is ConstInt -> return TypeNat()
            // If Const True/False, then it is Bool
            is ConstFalse, is ConstTrue -> return TypeBool()
            // If Expr is succ, when we need to typecheck inside succ
            is Succ -> {
                // Evaluate expr inside succ
                return visitSucc(expr, LinkedHashMap(iTable))
            }
            // Visit If statement
            is If -> {
                return visitIf(expr, LinkedHashMap(iTable),expType)
            }
            // Visit NatRec statement
            is NatRec -> {
                return visitNatRec(expr, LinkedHashMap(iTable),expType)
            }
            // Visit call of func/variable
            is Var -> {
                return visitVar(expr, LinkedHashMap(iTable))
            }
            // Visit application of function
            is Application -> {
                return visitApplication(expr, LinkedHashMap(iTable))
            }
            // Visit abstraction
            is Abstraction -> {
                return visitAbstraction(expr, LinkedHashMap(iTable),expType)
            }

            is Tuple -> {
                return visitTuple(expr, LinkedHashMap(iTable))
            }

            is DotTuple -> {
                return visitDotTuple(expr, LinkedHashMap(iTable))
            }

            is Match -> {
                return visitMatch(expr, LinkedHashMap(iTable), expType)
            }

            is ConstUnit -> {
                return TypeUnit()
            }
            is Inl -> return TypeSum(visitExpr(expr.expr_, LinkedHashMap(iTable), expType), null)
            is Inr -> return TypeSum(null, visitExpr(expr.expr_, LinkedHashMap(iTable),expType))

            is Sequence -> return visitSequence(expr, LinkedHashMap(iTable), expType)

            is Panic -> return expType

            is Deref -> return visitDeref(expr, LinkedHashMap(iTable))
            is Ref -> return TypeRef(visitExpr(expr.expr_, LinkedHashMap(iTable),expType))
            is Assign -> return visitAssign(expr, LinkedHashMap(iTable))
        }
        return TypeNat()
    }

    private fun visitAssign(expr: Assign, iTable: LinkedHashMap<String, Type>): Type {

        val type = visitExpr(expr.expr_1, LinkedHashMap(iTable), TypeUnit())
        if (type is TypeRef) {
            val type2 = visitExpr(expr.expr_2, LinkedHashMap(iTable),type.type_)
            if (type2 == type.type_) {
                return TypeUnit()
            }
            else {
                out.expected_got(type.type_, type2, "${expr.line_num}:${expr.col_num}")
            }
        }
        else {
            out.expected_got(TypeRef(null), type, "${expr.line_num}:${expr.col_num}")
        }
        return TypeUnit()
    }

    private fun visitDeref(expr: Deref, iTable: LinkedHashMap<String, Type>): Type {
        val type = visitExpr(expr.expr_, LinkedHashMap(iTable), TypeUnit())
        if (type is TypeRef) {
            return type.type_
        }
        else {
            out.expected_got(TypeRef(null), type, "${expr.line_num}:${expr.col_num}")
        }
        return TypeNat()
    }

    private fun visitSequence(expr: Sequence, iTable: LinkedHashMap<String, Type>, expType: Type): Type {
        var first = visitExpr(expr.expr_1, iTable,TypeUnit())
        if (first == TypeUnit()) {
            return visitExpr(expr.expr_2, iTable, expType)
        }
        else {
            out.expected_got(TypeUnit(), first, "${expr.line_num}:${expr.col_num}")
        }
        return TypeNat()

    }

    //TODO: Optimize this spaghetti code
    private fun visitMatch(match: Match, iTable: LinkedHashMap<String, Type>, expType: Type): Type {
        // Check if identifier is in table

        val ident = when (match.expr_) {
            is Var -> {

                match.expr_.stellaident_
            }
            else -> {
                out.expected_got(TypeSum(null,null),visitExpr(match.expr_, LinkedHashMap(iTable), TypeUnit()),"${match.line_num}:${match.col_num}")
            }
        }
        if (!iTable.containsKey(ident)) {
            out.undefined_variable(ident, "${match.line_num}:${match.col_num}")
        }

        val outTypes = ListType()
        for(it in match.listmatchcase_){
            when(it) {
                is AMatchCase -> {
                    outTypes.add(visitMatchCase(it, LinkedHashMap(iTable), ident.toString(),expType))
                }
            }
        }

        if (outTypes.size > 1) {
            when(val x =outTypes[0]) {
                is TypeSum -> {
                    when(val y = outTypes[1]) {
                        is TypeSum -> {
                            if(x.type_1 == null && y.type_1 == null) {
                                return TypeSum(null, combinesums(x.type_2,y.type_2))
                            }
                            else if(x.type_2 == null && y.type_2 == null) {
                                return TypeSum(combinesums(x.type_1,y.type_1), null)
                            }
                            else if (x.type_1 == y.type_1 || x.type_1 ==  y.type_2) {
                                out.match_error(match)
                            }
                            else {
                                return TypeSum(x.type_1 ?: y.type_1, x.type_2 ?: y.type_2)
                            }
                        }
                        else -> {
                            out.match_error(match)
                        }
                    }
                }
            }
            if (outTypes.distinct().size == 1) {
                return outTypes[0]
            }
            else {
                out.match_error(match)
            }
        }
        return TypeNat()
    }

    private fun combinesums(type1: Type, type2: Type): Type {
        return if(type1 == type2) {
            type1
        } else {
            out.expected_got(type1,type2,"")
            TypeNat()
        }
    }

    private fun visitMatchCase(matchCase: AMatchCase, iTable: LinkedHashMap<String, Type>, ident: String, expType: Type): Type {
        val outType : Type
        visitPattern(matchCase.pattern_, iTable, ident, matchCase.pattern_)
        return visitExpr(matchCase.expr_, LinkedHashMap(iTable), expType)
    }

    private fun visitPattern(pattern: Pattern, iTable: LinkedHashMap<String, Type>, inIdent: String, from: Pattern) {
        when(pattern){
            is PatternVar -> {
                val type = iTable[inIdent]
                when(from) {
                    is PatternInl -> {
                        when(type) {
                            is TypeSum -> {
                                iTable["${pattern.stellaident_}"] = type.type_1
                                return
                            }
                            else -> {
                                if (type != null) {
                                    out.expected_got(TypeSum(null,null),type,"${pattern.line_num}:${pattern.col_num}")
                                }
                            }
                        }
                    }
                    is PatternInr -> {
                            when(type) {
                                is TypeSum -> {
                                    iTable["${pattern.stellaident_}"] = type.type_2
                                    return
                                }
                                else -> {
                                    if (type != null) {
                                        out.expected_got(TypeSum(null,null),type,"${pattern.line_num}:${pattern.col_num}")
                                    }
                                }
                            }
                    }
                }
            }
            is PatternInl -> {
                visitPattern(pattern.pattern_, iTable, inIdent, pattern)
                return
            }
            is PatternInr -> {
                visitPattern(pattern.pattern_, iTable, inIdent, pattern)
                return
            }
        }
        return
    }


    private fun visitDotTuple(expr: DotTuple, iTable: LinkedHashMap<String, Type>): Type {
        when(val orig = visitExpr(expr.expr_, LinkedHashMap(iTable),TypeUnit())) {
            is TypeTuple -> {
                if (expr.integer_ > orig.listtype_.size && expr.integer_ > 0) {
                    out.unexpected_access_tuple(expr.integer_,orig.listtype_.size, orig ,"${expr.line_num}:${expr.col_num}")
                }
                return orig.listtype_[expr.integer_-1]
            }
            else -> {
                out.expected_got(TypeTuple(ListType()),orig,"${expr.line_num}:${expr.col_num}")
            }
        }
        return TypeNat()
    }

    private fun visitTuple(expr: Tuple, iTable: LinkedHashMap<String, Type>): Type {
        val listType = ListType()
        expr.listexpr_.forEach {
            when(it) {
                is Expr -> listType.add(visitExpr(it, LinkedHashMap(iTable),TypeUnit()))
            }
        }
        return TypeTuple(listType)
    }

    private fun visitAbstraction(expr: Abstraction, iTable: LinkedHashMap<String, Type>, expType: Type): Type {
        val inTypes = ListType()
        expr.listparamdecl_.forEach {
            when(it) {
                is AParamDecl -> {
                    iTable[it.stellaident_] = it.type_
                    inTypes.add(it.type_)
                }
            }
        }
        val outType = visitExpr(expr.expr_, LinkedHashMap(iTable),expType)
        return TypeFun(inTypes,outType)
    }

    private fun visitApplication(expr: Application, iTable: LinkedHashMap<String, Type>): Type {
        val fn = visitExpr(expr.expr_, LinkedHashMap(iTable), TypeUnit())

        when(fn) {
            is TypeFun -> {
                val arg = ListType()
                expr.listexpr_.forEach {
                    when(it) {
                        is Expr -> arg.add(visitExpr(it, LinkedHashMap(iTable),fn.listtype_[0]))
                    }
                }
                if (fn.listtype_.size == 1) {
                    if (!checkEq(fn.listtype_[0], arg[0])) {
                        out.expected_got(fn.listtype_[0],arg[0],"${expr.line_num}:${expr.col_num}")
                    }
                }
                return fn.type_
            }
            else -> {
                out.expected_got(TypeFun(ListType(),TypeUnit()),fn,"${expr.line_num}:${expr.col_num}")
            }
        }
        return TypeNat()
    }

    private fun checkEq(fn: Type, arg: Type?): Boolean {
        when(fn){
            is TypeSum -> {
                when(arg) {
                    is TypeSum -> {
                        return checkEq(fn.type_1,arg.type_1) || checkEq(fn.type_2,arg.type_2)
                    }
                    else -> {
                        return false
                    }
                }
            }
        }
        return fn == arg
    }

    /**
     * Visit Succ and check if input is Nat, report error otherwise
     * @param expr Succ to visit
     * @param iTable Type table
     * @return TypeNat if expr is Nat
     */
    private fun visitSucc(expr: Succ, iTable: LinkedHashMap<String, Type>): Type {
        when(val par = visitExpr(expr.expr_,LinkedHashMap(iTable),TypeNat())) {
            // If Nat, then return Nat
            is TypeNat -> return TypeNat()
            // If not, report error
            else -> out.expected_got(TypeNat(),par,"${expr.line_num}:${expr.col_num}")
        }
        return TypeNat()
    }

    /**
     * Visit If statement and check if condition is Bool, and branches are the same type, report error otherwise
     * @param if_ If statement to visit
     * @param iTable Type table
     * @return Type of if branches
     */
    private fun visitIf(if_: If, iTable: LinkedHashMap<String, Type>,expType: Type): Type {
        // Evaluate condition, then and else
        val cond_ = visitExpr(if_.expr_1, LinkedHashMap(iTable),TypeBool())
        val then_ = visitExpr(if_.expr_2, LinkedHashMap(iTable),expType)
        val else_ = visitExpr(if_.expr_3, LinkedHashMap(iTable),expType)
        // Check if condition is Bool
        if (cond_ != TypeBool()) {
            out.expected_got(TypeBool(),cond_,"${if_.line_num}:${if_.col_num}")
        }
        // Check if then and else are the same type
        if (then_ != else_) {
            out.expected_got(then_,else_,"${if_.line_num}:${if_.col_num}")
        }
        // Return type of then
        return then_
    }
    /**
     * Visit NatRec statement and check if b n is Nat, initial value is of type fn(Nat) -> Nat, and function is of type fn(Nat) -> Nat
     * @param natRec NatRec statement to visit
     * @param iTable Type table
     * @return Type
     */
    private fun visitNatRec (natRec: NatRec, iTable: LinkedHashMap<String, Type>,expType:Type): Type {
        // Evaluate count of recursion
        val n_ = visitExpr(natRec.expr_1,LinkedHashMap(iTable), TypeNat())
        // Evaluate initial value for recursion
        val z_ = visitExpr(natRec.expr_2,LinkedHashMap(iTable), expType)
        // Evaluate function to apply
        val f_ = visitExpr(natRec.expr_3,LinkedHashMap(iTable), expType)

        // Expected type for applied function
        val exp_inp_ = ListType()
        exp_inp_.add(z_)

        // Check if count is Nat
        if (n_ != TypeNat()) {
            out.expected_got(TypeNat(),n_,"${natRec.line_num}:${natRec.col_num}")
        }

        // f_ checks
        when(f_) {
            is TypeFun -> {
                // Check if applied function has 1 argument
                if (f_.listtype_.size != 1) {
                    out.few_arguments("${natRec.line_num}:${natRec.col_num}")
                }

                // Check if applied function has Nat as argument
                if (f_.listtype_[0] != TypeNat()) {
                    out.expected_got(TypeNat(),f_.listtype_[0],"${natRec.line_num}:${natRec.col_num}")
                }

                // Check if applied function has return type fn(z_.type) -> z_.type
                if (f_.type_ != TypeFun(exp_inp_,z_)) {
                    out.expected_got(
                        TypeFun(exp_inp_,z_),
                        f_.type_,
                        "${natRec.line_num}:${natRec.col_num}")
                }
            }
            else -> out.expected_got(
                TypeFun(exp_inp_,z_),
                f_,
                "${natRec.line_num}:${natRec.col_num}")
        }
        return z_

    }

    /**
     * Visit call of variable/function
     * @param sVar Identifier to visit
     * @param iTable Type table
     * @return Type of variable
     */
    private fun visitVar(sVar: Var, iTable: LinkedHashMap<String, Type>): Type {
        // Check if variable is in table
        if (iTable.containsKey(sVar.stellaident_)) {

            return iTable[sVar.stellaident_]!!
        }

        // Report error
        out.undefined_variable(sVar.stellaident_,"${sVar.line_num}:${sVar.col_num}")
        return TypeNat()
    }
}
