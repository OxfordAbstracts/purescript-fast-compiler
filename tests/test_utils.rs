/// Parse and re-emit JS through SWC to normalize formatting, then sort
/// imports, exports, and top-level var declarations alphabetically so that
/// ordering differences between compilers are ignored.
pub fn normalize_js(js: &str) -> String {
    use swc_common::{FileName, SourceMap, sync::Lrc};
    use swc_ecma_parser::{Parser, StringInput, Syntax, EsSyntax};
    use swc_ecma_codegen::{Emitter, text_writer::JsWriter};
    use swc_ecma_ast::*;

    let cm: Lrc<SourceMap> = Default::default();
    let fm = cm.new_source_file(
        Lrc::new(FileName::Custom("normalize".to_string())),
        js.to_string(),
    );

    let mut parser = Parser::new(
        Syntax::Es(EsSyntax::default()),
        StringInput::from(&*fm),
        None,
    );

    let mut module = parser.parse_module().expect("Failed to parse JS for normalization");

    // Sort export specifiers alphabetically
    let export_name = |n: &ExportSpecifier| -> String {
        match n {
            ExportSpecifier::Named(n) => match &n.exported {
                Some(ModuleExportName::Ident(id)) => id.sym.to_string(),
                None => match &n.orig {
                    ModuleExportName::Ident(id) => id.sym.to_string(),
                    _ => String::new(),
                },
                _ => String::new(),
            },
            _ => String::new(),
        }
    };
    for item in &mut module.body {
        if let ModuleItem::ModuleDecl(ModuleDecl::ExportNamed(export)) = item {
            export.specifiers.sort_by(|a, b| export_name(a).cmp(&export_name(b)));
        }
    }

    // Sort imports alphabetically by source path
    let import_src = |item: &ModuleItem| -> Option<String> {
        if let ModuleItem::ModuleDecl(ModuleDecl::Import(import)) = item {
            return Some(import.src.value.to_string_lossy().into_owned());
        }
        None
    };
    let import_indices: Vec<usize> = module.body.iter().enumerate()
        .filter_map(|(i, item)| import_src(item).map(|_| i))
        .collect();
    if !import_indices.is_empty() {
        let mut import_items: Vec<ModuleItem> = import_indices.iter()
            .map(|&i| module.body[i].clone())
            .collect();
        import_items.sort_by(|a, b| {
            let na = import_src(a).unwrap_or_default();
            let nb = import_src(b).unwrap_or_default();
            na.cmp(&nb)
        });
        for (slot, item) in import_indices.iter().zip(import_items) {
            module.body[*slot] = item;
        }
    }

    // Sort top-level var declarations alphabetically
    let decl_name = |item: &ModuleItem| -> Option<String> {
        if let ModuleItem::Stmt(Stmt::Decl(Decl::Var(var_decl))) = item {
            if let Some(decl) = var_decl.decls.first() {
                if let Pat::Ident(ident) = &decl.name {
                    return Some(ident.sym.to_string());
                }
            }
        }
        None
    };
    let var_indices: Vec<usize> = module.body.iter().enumerate()
        .filter_map(|(i, item)| decl_name(item).map(|_| i))
        .collect();
    if !var_indices.is_empty() {
        let mut var_items: Vec<ModuleItem> = var_indices.iter()
            .map(|&i| module.body[i].clone())
            .collect();
        var_items.sort_by(|a, b| {
            let na = decl_name(a).unwrap_or_default();
            let nb = decl_name(b).unwrap_or_default();
            na.cmp(&nb)
        });
        for (slot, item) in var_indices.iter().zip(var_items) {
            module.body[*slot] = item;
        }
    }

    // Emit normalized JS
    let mut buf = Vec::new();
    {
        let writer = JsWriter::new(cm.clone(), "\n", &mut buf, None);
        let mut emitter = Emitter {
            cfg: swc_ecma_codegen::Config::default().with_minify(false),
            cm: cm.clone(),
            comments: None,
            wr: writer,
        };
        emitter.emit_module(&module).expect("Failed to emit JS");
    }

    let js = String::from_utf8(buf).expect("Invalid UTF-8 in emitted JS");
    // Strip standalone empty statements
    let js: String = js.lines()
        .filter(|line| line.trim() != ";")
        .collect::<Vec<_>>()
        .join("\n");
    // Normalize error messages
    let re = regex::Regex::new(
        r#"throw new Error\("Failed pattern match[^"]*"\s*\+\s*\[[^\]]*\]\)"#
    ).unwrap();
    let js = re.replace_all(&js, r#"throw new Error("Failed pattern match")"#).to_string();
    let re2 = regex::Regex::new(
        r#"throw Error\("Failed pattern match[^"]*"\)"#
    ).unwrap();
    let js = re2.replace_all(&js, r#"throw new Error("Failed pattern match")"#).to_string();
    let re3 = regex::Regex::new(
        r#"throw new Error\("Failed pattern match[^"]*"\s*\+\s*\[\s*\n[^\]]*\]\)"#
    ).unwrap();
    let js = re3.replace_all(&js, r#"throw new Error("Failed pattern match")"#).to_string();
    js
}
