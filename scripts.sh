#! /bin/bash

exercify () {
  sed '
#    /:= by$/, /^  done$/ {/:= by$/!{/^  done$/!{/^  /d;};};}
#    /^ [ ·]*have.* := by$/{d;}
#    s=^\(   *\)done$=\1sorry\n&=
    /:= by$/, /^   *done$/ {/:= by$/!{/^   *done$/!{/^  /d;};};}
    /^  *have.* := by$/{d;}
    s=^\(   *\)done=\1sorry\n&=
    ' "${1}"
}

exme () {
  newPth="${1/.lean/_no_sols.lean}"
  echo ${newPth}
  exercify "${1}" > "${newPth}"
}

mkNew () {
  local tl="$(ls MA4N1/L* | sed -n 's=MA4N1/L0*\([0-9][0-9]*\)_.*=\1=p' | tail -1)"
  tl="$(printf '%02d' "$(( tl + 1 ))")"
  local file="$( printf 'MA4N1/L%s_%s.lean' "${tl}" "${1// /_}" )"
  if [ -f "${file}" ]; then
    lcyan $'File' ; printf ' %s ' "${file}" ; lcyan $'already exists!\n'
  else
    { brown $'save to file '; printf '%s\n' "${file}" ; } >&2
    printf $'import Mathlib.Tactic\n\n#allow_unused_tactic Lean.Parser.Tactic.done\n\nnamespace TPwL\n\n\n\nend TPwL\n' > "${file}"
  fi
}

genToc () {
  printf '#  Table of Contents\n\n'
  local fil
  for fil in MA4N1/*.lean
  do
    printf '[%s](%s) (%s)\n\n' "$( sed -n '/^# /{s=^#  *==p;q}' "${fil}" )" "${fil}" "${fil}"
  done |
    grep -v "easy\|week_end\|no_sols\|\[\]"
}

alias toc='( croot ; genToc > toc.md )'
