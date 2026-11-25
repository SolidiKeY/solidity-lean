// Shared editor eligibility; compiler/RPC source admission is unchanged.
'use strict';
const {extname}=require('node:path');
const selector={scheme:'file',language:'solidity',pattern:'**/*.sol'};
function isSolidityFile(doc){return !!doc&&!doc.isClosed&&doc.languageId==='solidity'&&doc.uri?.scheme==='file'&&typeof doc.uri.fsPath==='string'&&extname(doc.uri.fsPath).toLowerCase()==='.sol';}
module.exports={selector,isSolidityFile};
