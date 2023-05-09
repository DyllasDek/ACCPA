package org.stella.typecheck


import org.stella.TypeErrorOut
import org.syntax.stella.Absyn.*
import org.syntax.stella.Absyn.Record
import java.util.*
import kotlin.collections.LinkedHashMap

object TypeCheck {
    private var out: TypeErrorOut = TypeErrorOut()
    private var identTypes: LinkedHashMap<String, Type> = LinkedHashMap()

    @Throws(Exception::class)
    fun typecheckProgram(program: Program) {
        when (program) {
            is AProgram -> program.listdecl_.map {
                when (it) {
                    is DeclFun-> {
                        visitDeclFn(it.stellaident_,it.listparamdecl_,it.returntype_,it.expr_,LinkedHashMap(identTypes))
                    }
                    is DeclFunGeneric -> {
                        visitDeclFn(it.stellaident_,it.listparamdecl_,it.returntype_,it.expr_,LinkedHashMap(identTypes))
                        for ( name in it.liststellaident_){
                            if (!(identTypes[it.stellaident_] as TypeFun).listtype_.contains(TypeVar(name))) {
                                (identTypes[it.stellaident_] as TypeFun).listtype_.add(TypeVar(name))
                            }
                        }
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
    private fun visitDeclFn(name:String,params:ListParamDecl,ret:ReturnType,expr:Expr, iTable: LinkedHashMap<String, Type>) {
        // Add all params to Type Table at current scope
        val inTypes = ListType()
        params.forEach {
            when(it) {
                is AParamDecl -> {
                    iTable[it.stellaident_] = it.type_
                    inTypes.add(it.type_)
                }
            }
        }
        // Evaluate expression and get its type

        if (ret is SomeReturnType) {
            val actualType = visitExpr(expr, LinkedHashMap(iTable), ret.type_)

            val shouldReturn = ret.type_

            if (!checkEq(shouldReturn,actualType,iTable)) {
                // Report error
                out.expected_got(ret.type_,actualType,name)
            }
            identTypes[name] = TypeFun(inTypes,actualType)
        }


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
                return visitApplication(expr, iTable)
            }
            // Visit abstraction
            is Abstraction -> {
                return visitAbstraction(expr, LinkedHashMap(iTable),expType)
            }

            is Equal -> {
                val l = visitExpr(expr.expr_1, LinkedHashMap(iTable),expType)
                val r = visitExpr(expr.expr_2, LinkedHashMap(iTable),expType)
                if (l != r) {
                    out.expected_got(l,r,"${expr.line_num}:${expr.col_num}")
                }
                return TypeBool()
            }
            is Divide -> {
                val l = visitExpr(expr.expr_1, LinkedHashMap(iTable),expType)
                val r = visitExpr(expr.expr_2, LinkedHashMap(iTable),expType)
                if (l != TypeNat()) {
                    out.expected_got(TypeNat(),l,"${expr.line_num}:${expr.col_num}")
                } else if (r != TypeNat()) {
                    out.expected_got(TypeNat(),r,"${expr.line_num}:${expr.col_num}")
                }
                return TypeNat()
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


            is Record -> return visitRecord(expr, LinkedHashMap(iTable))
            is DotRecord -> return visitDotRecord(expr, LinkedHashMap(iTable))

            is TypeAbstraction -> {
                val params = ListType()
                expr.liststellaident_.forEach {
                    iTable[it] = TypeVar(it)
                    params.add(TypeVar(it))
                }
                val type = visitExpr(expr.expr_, LinkedHashMap(iTable), expType)
                if (type is TypeFun) {
                    return TypeFun(params,type.type_)
                }
            }
            is TypeApplication -> {
                val func = visitExpr(expr.expr_, LinkedHashMap(iTable), expType)
                if (func is TypeFun) {
                    func.listtype_.zip(expr.listtype_) { name, type ->
                        if (name is TypeVar) {
                            iTable[name.stellaident_] = type
                        }
                    }
                    return visitExpr(expr.expr_, iTable, expType)
                } else {
                    out.expected_got(TypeFun(ListType(),TypeNat()),func,"${expr.line_num}:${expr.col_num}")
                }
            }
        }
        return TypeNat()
    }

    private fun visitDotRecord(expr: DotRecord, iTable: LinkedHashMap<String, Type>): Type {
        val type = visitExpr(expr.expr_, LinkedHashMap(iTable), TypeUnit())
        if (type is TypeRecord) {
            val recordBody = type.listrecordfieldtype_
            val field = recordBody.find {
                if (it is ARecordFieldType) {
                    it.stellaident_ == expr.stellaident_
                }
                else {
                    false
                }
            }
            if (field != null && field is ARecordFieldType){
                return field.type_
            }
            else {
                out.field_not_found(expr.stellaident_, "${expr.line_num}:${expr.col_num}")
            }
        }
        else {
            out.expected_got(TypeRecord(ListRecordFieldType()), type, "${expr.line_num}:${expr.col_num}")
        }
        return TypeNat()
    }

    private fun visitRecord(expr: Record, iTable: LinkedHashMap<String, Type>): Type {
        val recordBody = ListRecordFieldType()
        expr.listbinding_.forEach {
            when (it) {
                is ABinding -> {
                    recordBody.add(ARecordFieldType(it.stellaident_, visitExpr(it.expr_, LinkedHashMap(iTable),TypeUnit())))
                }
            }
        }
        return TypeRecord(recordBody)
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
        val first = visitExpr(expr.expr_1, iTable,TypeUnit())
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
                                return TypeSum(null, combineSums(x.type_2,y.type_2))
                            }
                            else if(x.type_2 == null && y.type_2 == null) {
                                return TypeSum(combineSums(x.type_1,y.type_1), null)
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

    private fun combineSums(type1: Type, type2: Type): Type {
        return if(type1 == type2) {
            type1
        } else {
            out.expected_got(type1,type2,"")
            TypeNat()
        }
    }

    private fun visitMatchCase(matchCase: AMatchCase, iTable: LinkedHashMap<String, Type>, ident: String, expType: Type): Type {
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
                                iTable[pattern.stellaident_] = type.type_1
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
                                    iTable[pattern.stellaident_] = type.type_2
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
        val outType : Type = if (expType is TypeFun){
            visitExpr(expr.expr_, LinkedHashMap(iTable),expType.type_)
        } else {
            visitExpr(expr.expr_, LinkedHashMap(iTable),TypeUnit())
        }
        return TypeFun(inTypes,outType)
    }

    private fun visitApplication(expr: Application, iTable: LinkedHashMap<String, Type>): Type {
        when(val fn = visitExpr(expr.expr_, iTable, TypeUnit())) {
            is TypeFun -> {
                val arg = ListType()
                expr.listexpr_.forEach {
                    when(it) {
                        is Expr -> arg.add(visitExpr(it, LinkedHashMap(iTable),fn.listtype_[0]))
                    }
                }
                if (fn.listtype_.size == 1) {
                    if (!checkEq(fn.listtype_[0], arg[0],iTable)) {
                        out.expected_got(fn.listtype_[0],arg[0],"${expr.line_num}:${expr.col_num}")
                    }
                }
                return evalVar(fn.type_, iTable)
            }
            else -> {
                out.expected_got(TypeFun(ListType(),TypeUnit()),fn,"${expr.line_num}:${expr.col_num}")
            }
        }
        return TypeNat()
    }
    private fun evalVar (inp: Type, iTable: LinkedHashMap<String, Type>) : Type {
        if (inp is TypeVar) {
            if (iTable.contains(inp.stellaident_)) {
                return iTable[inp.stellaident_]!!
            } else {
                out.expected_got(TypeVar(""),inp,"")
            }
        }
        return inp
    }
    private fun checkEq(exp: Type?, act: Type?, iTable: LinkedHashMap<String, Type>): Boolean {
        return if (exp is TypeSum && act is TypeSum) {
            checkEq(exp.type_1,act.type_1, iTable) || checkEq(exp.type_2,act.type_2, iTable)
        }
        else if (exp is TypeRecord && act is TypeRecord) {
                act.listrecordfieldtype_.containsAll(exp.listrecordfieldtype_)
        }
        else if (exp is TypeFun && act is TypeFun) {
            checkEq(act.listtype_[0],exp.listtype_[0], iTable) && checkEq(exp.type_,act.type_, iTable)
        }
        else if (exp is TypeForAll) {
            checkEq(exp.type_,act, iTable)
        }
        else if (exp is TypeVar && act is TypeVar && !iTable.contains(act.stellaident_) && iTable.contains(exp.stellaident_)) {
            true
        }
        else if (exp is TypeVar && iTable.contains(exp.stellaident_) && iTable[exp.stellaident_] !is TypeVar) {
            checkEq(iTable[exp.stellaident_],act, iTable)
        }
        else if (act is TypeVar && iTable.contains(act.stellaident_) && iTable[act.stellaident_] !is TypeVar) {
            checkEq(exp,iTable[act.stellaident_], iTable)
        }
        else if(exp is TypeVar  && act is TypeVar ) {
            exp.stellaident_ == act.stellaident_
        }
        else {
            exp == act
        }
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
     * @param ifExp If statement to visit
     * @param iTable Type table
     * @return Type of if branches
     */
    private fun visitIf(ifExp: If, iTable: LinkedHashMap<String, Type>, expType: Type): Type {
        // Evaluate condition, then and else
        val cond = visitExpr(ifExp.expr_1, LinkedHashMap(iTable),TypeBool())
        val th = visitExpr(ifExp.expr_2, LinkedHashMap(iTable),expType)
        val els = visitExpr(ifExp.expr_3, LinkedHashMap(iTable),expType)
        // Check if condition is Bool
        if (cond != TypeBool()) {
            out.expected_got(TypeBool(),cond,"${ifExp.line_num}:${ifExp.col_num}")
        }
        // Check if then and else are the same type
        if (th != els) {
            out.expected_got(th,els,"${ifExp.line_num}:${ifExp.col_num}")
        }
        // Return type of then
        return th
    }
    /**
     * Visit NatRec statement and check if b n is Nat, initial value is of type fn(Nat) -> Nat, and function is of type fn(Nat) -> Nat
     * @param natRec NatRec statement to visit
     * @param iTable Type table
     * @return Type
     */
    private fun visitNatRec (natRec: NatRec, iTable: LinkedHashMap<String, Type>,expType:Type): Type {
        // Evaluate count of recursion
        val n = visitExpr(natRec.expr_1,LinkedHashMap(iTable), TypeNat())
        // Evaluate initial value for recursion
        val z = visitExpr(natRec.expr_2,LinkedHashMap(iTable), expType)
        // Evaluate function to apply
        val f = visitExpr(natRec.expr_3,LinkedHashMap(iTable), expType)

        // Expected type for applied function
        val expInp = ListType()
        expInp.add(z)

        // Check if count is Nat
        if (n != TypeNat()) {
            out.expected_got(TypeNat(),n,"${natRec.line_num}:${natRec.col_num}")
        }

        // f_ checks
        when(f) {
            is TypeFun -> {
                // Check if applied function has 1 argument
                if (f.listtype_.size != 1) {
                    out.few_arguments("${natRec.line_num}:${natRec.col_num}")
                }

                // Check if applied function has Nat as argument
                if (f.listtype_[0] != TypeNat()) {
                    out.expected_got(TypeNat(),f.listtype_[0],"${natRec.line_num}:${natRec.col_num}")
                }

                // Check if applied function has return type fn(z_.type) -> z_.type
                if (f.type_ != TypeFun(expInp,z)) {
                    out.expected_got(
                        TypeFun(expInp,z),
                        f.type_,
                        "${natRec.line_num}:${natRec.col_num}")
                }
            }
            else -> out.expected_got(
                TypeFun(expInp,z),
                f,
                "${natRec.line_num}:${natRec.col_num}")
        }
        return z

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
