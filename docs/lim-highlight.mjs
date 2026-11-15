// A lossless lexical colorizer, not a parser. Used at build time and in the editor.
// Scan complete tokens so strings/comments cannot inject markup or color keywords.
const token = /\/\/[^\r\n]*|"(?:\\[\s\S]|[^"\\])*"?|#\\(?:u\{[\da-fA-F]+\}|[^\s(){}\[\];]+|[^\r\n])|[+-]?\d[\d_]*(?:\.\d[\d_]*)?[eE][+-]?\d+(?:f(?:32|64))?(?=$|[\s(){}\[\];,:])|[^\s(){}\[\];"=<>!+*%&|^,:/]+(?:::[^\s(){}\[\];"=<>!+*%&|^,:/]+)*|[<>!=+*%&|^:/-]+|[\s\S]/gu;
const number = /^[+-]?(?:\d[\d_]*(?:\.\d[\d_]*)?(?:[eE][+-]?\d+)?|0[xX][\da-fA-F_]+|0[bB][01_]+)(?:[ui](?:8|16|32|64|128|size)|f(?:32|64))?$/u;
export function escapeHTML(text) {
  return text.replace(/[&<>"']/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' })[c]);
}
export function highlightLim(source) {
  return Array.from(source.matchAll(token), ([text]) => {
    let kind = '';
    if (text.startsWith('//')) kind = 'comment';
    else if (text.startsWith('"') || text.startsWith('#\\')) kind = 'string';
    else if (number.test(text) || /^(?:true|false)$/.test(text)) kind = 'literal';
    else if (/^#(?:u(?:8|16|32|64|128|size)|i(?:8|16|32|64|128|size)|f(?:32|64)|bool|char)$/.test(text)) kind = 'type';
    else if (/^#[\w-]+::[\w:-]+$/.test(text) || /^[<>!=+*%&|^:/-]+$/.test(text)) kind = 'operator';
    else if (/^#[a-z][\w-]*$/.test(text)) kind = 'keyword';
    const escaped = escapeHTML(text);
    return kind ? `<span class="lim-${kind}">${escaped}</span>` : escaped;
  }).join('');
}
