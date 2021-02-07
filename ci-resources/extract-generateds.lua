local element_pat = "^  .*$"
local file_line_pat = "^  (%b\"\")"
local generated_pat = "^  %(generated%)$"
local generated = false
local generated_files = {}
for line in io.lines() do
  local is_file = string.match( line, element_pat, 0 )
  local is_generated = string.match(line, generated_pat, 0)
  if is_generated then
    generated = true
  elseif is_file then
    local file_entry = string.match(line, file_line_pat, 0)
    if file_entry then
      local local_name = string.match(file_entry, "^\"([^/].*)\"$")
      if local_name and generated then
        table.insert( generated_files,local_name )
      end
    end
  else
    generated = false
  end
end

for _,v in ipairs(generated_files) do
  print(v)
end