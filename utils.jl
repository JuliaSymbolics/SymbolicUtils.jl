# Thanks @tlienart

using Markdown

function hfun_doc(params)
    fname = params[1]
    head = length(params) > 1 ? params[2] : fname
    type = length(params) == 3 ? params[3] : ""
    mod = length(params) == 4 ? params[4] : ""
    if mod != ""
        doc = eval(Meta.parse("using SymbolicUtils; @doc SymbolicUtils.$mod.$fname"))
    else
        doc = eval(Meta.parse("using SymbolicUtils; @doc SymbolicUtils.$fname"))
    end
    txt = Markdown.plain(doc)
    # possibly further processing here
    body = Franklin.fd2html(txt, internal=true)
    return """
      <div class="docstring">
          <h2 class="doc-header" id="$fname">
            <a href="#$fname">$head</a>
            <div class="doc-type">$type</div></h2>
          <div class="doc-content">$body</div>
      </div>
    """
end
