package output

import (
	"encoding/json"
	"io"
	"reflect"
)

func WriteJSONLines(w io.Writer, values any) error {
	v := reflect.ValueOf(values)
	enc := json.NewEncoder(w)
	enc.SetEscapeHTML(false)
	if v.Kind() != reflect.Slice && v.Kind() != reflect.Array {
		return enc.Encode(values)
	}
	for i := 0; i < v.Len(); i++ {
		if err := enc.Encode(v.Index(i).Interface()); err != nil {
			return err
		}
	}
	return nil
}
