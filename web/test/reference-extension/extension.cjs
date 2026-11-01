'use strict';
// Read-only inspection of the real extension's public testing API. Install in
// an isolated reference host, never in the offline IDE's production runtime.
const vscode=require('vscode');
const fs=require('node:fs');
exports.activate=context=>{
  context.subscriptions.push(vscode.commands.registerCommand('solidityLeanParity.capture',async()=>{
    const file=process.env.SOLIDITY_LEAN_REFERENCE_REPORT;
    if(!file)throw new Error('Set SOLIDITY_LEAN_REFERENCE_REPORT for the isolated reference host');
    const document=vscode.window.activeTextEditor?.document;
    if(!document||document.languageId!=='solidity')throw new Error('Open the comparison Solidity file');
    const api=await vscode.extensions.getExtension('SolidiKeY.solidity-lean').activate();
    const report={startedAt:new Date().toISOString(),source:document.getText(),trials:[]};
    try{
      for(let i=0;i<3;i++){
        const start=performance.now();const result=await api.verify(document);
        report.trials.push({elapsedMs:+(performance.now()-start).toFixed(1),report:result});
        if(!result||result.errors.length)throw new Error('Reference verification did not complete');
      }
      report.diagnostics=vscode.languages.getDiagnostics(document.uri).map(d=>({message:d.message,severity:d.severity,code:d.code,range:d.range}));
      const row=report.trials[0].report.results.find(r=>r.function==='one');
      if(row)report.hover=await vscode.commands.executeCommand('vscode.executeHoverProvider',document.uri,new vscode.Position(row.range.start.line,row.range.start.character));
      report.tests=[...api.controller.items].flatMap(([,file])=>[...file.children].map(([,item])=>({label:item.label,description:item.description})));
      report.passed=report.trials.every(t=>t.report.results.find(r=>r.function==='one')?.status==='proved'&&t.report.results.find(r=>r.function==='openGoal')?.status==='pending');
    }catch(error){report.error=error.stack;report.passed=false;}
    fs.writeFileSync(file,JSON.stringify(report,null,2)+'\n');
    if(!report.passed)vscode.window.showErrorMessage('Reference parity capture failed; inspect its JSON report.');
  }));
};
