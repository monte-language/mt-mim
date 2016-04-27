import "lib/codec/utf8" =~ [=> UTF8 :DeepFrozen]
exports (main)

def decodeMAST(bs :Bytes, ej) as DeepFrozen:
    # Magic number.
    def b`Mont$\xe0MAST$\x00@{var stream}` exit ej := bs
    def patts := [].diverge()
    def exprs := [].diverge()

    def decodeInt() :Int:
        var shift :Int := 0
        var i :Int := 0
        while (true):
            def b :Int := stream[0]
            stream slice= (1)
            i |= (b & 0x7f) << shift
            shift += 7
            if ((b & 0x80) != 0x80):
                break
        return i

    def decodeStr() :Str:
        def size := decodeInt()
        def via (UTF8.decode) s :Str exit ej := stream.slice(0, size)
        stream slice= (size)
        return s

    def decodeExpr():
        def i := decodeInt()
        return try:
            exprs[i]
        catch _:
            throw.eject(ej, "Invalid MAST expression index")

    def decodeExprs():
        def size := decodeInt()
        if (size == 0) {return []}
        return [for _ in (0..!size) decodeExpr()]

    def decodePatt():
        def i := decodeInt()
        return try:
            patts[i]
        catch _:
            throw.eject(ej, "Invalid MAST pattern index")

    def decodePatts():
        def size := decodeInt()
        if (size == 0) {return []}
        return [for _ in (0..!size) decodePatt()]

    while (stream.size() != 0):
        traceln(`Stream has ${stream.size()} elts remaining`)
        traceln(`Exprs: ${exprs.size()} Patts: ${patts.size()}`)
        switch (stream):
            match b`LN@rest`:
                stream := rest
                exprs.push("NullExpr")
            match b`LC@rest`:
                for i in (1..4):
                    def via (UTF8.decode) c exit __continue := rest.slice(0, i)
                    stream := rest.slice(i)
                    exprs.push(["CharExpr", c[0]])
                    break
                throw.eject(ej, "Invalid MAST character")
            match b`LD@rest`:
                def dbs := rest.slice(0, 8)
                stream := rest.slice(8)
                def d := _makeDouble.fromBytes(_makeList.fromIterable(dbs))
                exprs.push(["DoubleExpr", d])
            match b`LI@rest`:
                stream := rest
                var i := decodeInt()
                i := if ((i & 0x01) == 0x01) { (i >> 1) ^ -1 } else { i >> 1 }
                exprs.push(["IntExpr", i])
            match b`LS@rest`:
                stream := rest
                def s := decodeStr()
                exprs.push(["StrExpr", s])
            match b`L@_`:
                throw.eject(ej, "Invalid MAST literal")
            match b`PA@rest`:
                stream := rest
                def expr := decodeExpr()
                def patt := decodePatt()
                patts.push(["ViaPatt", expr, patt])
            match b`PB@rest`:
                stream := rest
                def name := decodeStr()
                patts.push(["BindingPatt", name])
            match b`PF@rest`:
                stream := rest
                def name := decodeStr()
                def guard := decodeExpr()
                patts.push(["FinalPatt", name, guard])
            match b`PI@rest`:
                stream := rest
                def guard := decodeExpr()
                patts.push(["IgnorePatt", guard])
            match b`PL@rest`:
                stream := rest
                def patts := decodePatts()
                patts.push(["ListPatt", patts])
            match b`PV@rest`:
                stream := rest
                def name := decodeStr()
                def guard := decodeExpr()
                patts.push(["VarPatt", name, guard])
            match b`P@_`:
                throw.eject(ej, "Invalid MAST pattern")
            match b`A@rest`:
                stream := rest
                def target := decodeStr()
                def rhs := decodeExpr()
                exprs.push(["AssignExpr", target, rhs])
            match b`B@rest`:
                stream := rest
                def name := decodeStr()
                exprs.push(["BindingExpr", name])
            match b`C@rest`:
                stream := rest
                def obj := decodeExpr()
                def verb := decodeStr()
                def args := decodeExprs()
                def namedArgSize := decodeInt()
                def namedArgs := if (namedArgSize == 0) {[]} else {
                    [for _ in (0..!namedArgSize) [decodeExpr(), decodeExpr()]]
                 }
                exprs.push(["CallExpr", obj, verb, args, namedArgs])
            match b`D@rest`:
                stream := rest
                def patt := decodePatt()
                def ex := decodeExpr()
                def rhs := decodeExpr()
                exprs.push(["DefExpr", patt, ex, rhs])
            match b`e@rest`:
                stream := rest
                def patt := decodePatt()
                def expr := decodeExpr()
                exprs.push(["EscapeExpr", patt, expr])
            match b`E@rest`:
                stream := rest
                def patt := decodePatt()
                def expr := decodeExpr()
                def catchPatt := decodePatt()
                def catchExpr := decodeExpr()
                exprs.push(["EscapeExpr", patt, expr, catchPatt, catchExpr])
            match b`F@rest`:
                stream := rest
                def tryExpr := decodeExpr()
                def finallyExpr := decodeExpr()
                exprs.push(["FinallyExpr", tryExpr, finallyExpr])
            match b`H@rest`:
                stream := rest
                exprs.push(["HideExpr", decodeExpr()])
            match b`I@rest`:
                stream := rest
                def cond := decodeExpr()
                def cons := decodeExpr()
                def alt := decodeExpr()
                exprs.push(["IfExpr", cond, cons, alt])
            match b`M@rest`:
                stream := rest
                def doc := decodeStr()
                def verb := decodeStr()
                def patts := decodePatts()
                def namedPattSize := decodeInt()
                def namedPatts := if (namedPattSize == 0) {[]} else {
                    [for _ in (0..!namedPattSize)
                     [decodeExpr(), decodePatt(), decodeExpr()]]
                }
                def guard := decodeExpr()
                def body := decodeExpr()
                exprs.push(["MethodExpr", doc, verb, patts, namedPatts, guard,
                            body])
            match b`N@rest`:
                stream := rest
                def name := decodeStr()
                exprs.push(["NounExpr", name])
            match b`O@rest`:
                stream := rest
                def doc := decodeStr()
                def patt := decodePatt()
                def asExpr := decodeExpr()
                def auditors := decodeExprs()
                def methods := decodeExprs()
                def matchers := decodeExprs()
                exprs.push(["ObjExpr", doc, patt, asExpr, auditors, methods,
                            matchers])
            match b`R@rest`:
                stream := rest
                def patt := decodePatt()
                def body := decodeExpr()
                exprs.push(["MatcherExpr", patt, body])
            match b`S@rest`:
                stream := rest
                exprs.push(["SeqExpr", decodeExprs()])
            match b`T@rest`:
                stream := rest
                exprs.push("MetaStateExpr")
            match b`X@rest`:
                stream := rest
                exprs.push("MetaContextExpr")
            match b`Y@rest`:
                stream := rest
                def tryExpr := decodeExpr()
                def catchPatt := decodePatt()
                def catchExpr := decodeExpr()
                exprs.push(["TryExpr", tryExpr, catchPatt, catchExpr])
            match _:
                throw.eject(ej, "Couldn't match any MAST node")
    return exprs.pop()

def main(argv, => makeFileResource, => makeStdOut) as DeepFrozen:
    def path := argv.last()
    def handle := makeFileResource(path)
    def stdout := makeStdOut()
    return when (def bs := handle<-getContents()) ->
        def ast := decodeMAST(bs, null)
        def via (UTF8.encode) s := M.toQuote(ast)
        stdout<-receive(s)
        0
