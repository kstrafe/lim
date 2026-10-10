-- Requires Neovim's built-in LSP client and `lim lsp` on PATH.
-- Set vim.g.lim_lsp_cmd = { '/path/to/lim', 'lsp' } to override.
-- Disable automatic startup when another integration (e.g. lspconfig) owns it.
if vim.g.lim_lsp_autostart == false then return end
if vim.b.lim_lsp_started then return end
vim.b.lim_lsp_started = true
local root = vim.fs.root(0, { 'lim.lsp', 'lim.project', '.git' }) or vim.fn.getcwd()
vim.lsp.start({
  name = 'lim',
  cmd = vim.g.lim_lsp_cmd or { 'lim', 'lsp' },
  root_dir = root,
})
