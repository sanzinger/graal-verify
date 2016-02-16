package at.sanzinger.boolector.dump;

import java.io.IOException;
import java.io.OutputStream;
import java.io.OutputStreamWriter;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.stream.JsonWriter;

import at.sanzinger.boolector.CheckResult;

/**
 * Dumps verification results as JSON to the output stream.
 */
public class JSONDumper {
    private static final GsonBuilder builder = new GsonBuilder().setPrettyPrinting();
    private final OutputStream outputStream;
    private Gson gson;
    private JsonWriter jsonWriter;

    public JSONDumper(OutputStream outputStream) {
        super();
        this.outputStream = outputStream;
    }

    private Gson getGson() {
        if (gson == null) {
            gson = builder.setPrettyPrinting().create();
        }
        return gson;
    }

    private JsonWriter getJsonWriter() throws IOException {
        if (jsonWriter == null) {
            OutputStreamWriter writer = new OutputStreamWriter(outputStream);
            jsonWriter = new JsonWriter(writer);
            jsonWriter.beginArray();
        }
        return jsonWriter;
    }

    public synchronized void dump(String name, CheckResult[] result) {
        JsonObject o = new JsonObject();
        JsonElement resultTree = getGson().toJsonTree(result);
        o.add("name", getGson().toJsonTree(name));
        o.add("result", resultTree);
        try {
            JsonWriter writer = getJsonWriter();
            getGson().toJson(o, writer);
            writer.flush();
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    public void close() {
        if (jsonWriter != null) {
            try {
                jsonWriter.endArray();
                jsonWriter.close();
            } catch (IOException e) {
                throw new RuntimeException(e);
            }
        }
    }
}
