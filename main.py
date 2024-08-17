import ast
import json
import os
import subprocess
from flask import Flask
from flask import request
from flask_restful import Api, Resource, reqparse
from flask_cors import CORS




app = Flask(__name__)
api = Api()
CORS(app)

#parser = reqparse.RequestParser()
#parser.add_argument("name", type=str)

class Main(Resource):
    def get(self, course_id):
        pass

    def delete(self, course_id):
        pass

    def post(self):
        upload = request.files.get('upload')
        name, ext = os.path.splitext(upload.filename)
        if ext not in ('.bpmn', '.json'):
            return "File extension not allowed."

        save_path = "/tmp"
        if not os.path.exists(save_path):
            os.makedirs(save_path)

        file_path = "{path}/{file}".format(path=save_path, file=upload.filename)
        upload.save(file_path)
        # return "File successfully saved to '{0}'.".format(save_path)
        #responseble = dyno.main(file_path, shell=True)
        p = subprocess.run("python dyno.py " + file_path, shell=True)
        #print(responseble)
        if not p.returncode:
            with open('temp.json', 'r') as f:
                json_data = ast.literal_eval(f.readline())
                return json_data
        else:
            return "Код ошибки запуска модели " + str(p.returncode)


        #print(files.get('upload'))
        #return dyno.main(files.get('upload')[0])

    def init(a):
        global d
        d = a
        print(d)
    def put(self, course_id):
        pass


api.add_resource(Main, "/api/")
api.init_app(app)


if __name__ == "__main__":
    app.run(debug=True, host="localhost", port=3000)



