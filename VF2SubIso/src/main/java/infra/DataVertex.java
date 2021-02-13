package infra;

public class DataVertex extends Vertex {


    private String vertexURI="";
//    private final int hashValue;


    public DataVertex(String uri, String type) {
        super(type.toLowerCase());
        this.vertexURI=uri.toLowerCase();
        // ???: Is Integer large enough for our use case of possible 10+ million vertices? [2021-02-07]
//        this.hashValue=vertexURI.hashCode();
    }

    @Override
    public String toString() {
        return "vertex{" +
                "type='" + getTypes() + '\'' +
                ", attributes=" + super.getAllAttributesList() +
                '}';
    }

//    public int getHashValue() {
//        return hashValue;
//    }

    public String getVertexURI() {
        return vertexURI;
    }

    @Override
    public boolean isEqual(Vertex v) {
        if (!super.getTypes().containsAll(v.getTypes()))
            return false;
        if(!super.getAllAttributesNames().containsAll(v.getAllAttributesNames()))
            return false;
        for (Attribute attr:v.getAllAttributesList())
            if(!attr.isNull() && !super.getAttributeByName(attr.getAttrName()).equals(attr.getAttrValue()))
                return false;
        return true;
    }
}