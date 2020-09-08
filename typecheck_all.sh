find . -iname '*.agda' -exec agda --no-main --library=standard-library --library=computability '{}' ';'
