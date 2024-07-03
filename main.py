import json
import os
import subprocess
import click
from flask import Flask
from flask import request
from flask_restful import Api, Resource, reqparse
import requests


import dyno
from bottle import static_file
from dyno import GrandSolver, get_variable, fill_template

app = Flask(__name__)
api = Api()

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
        p = subprocess.run("python dyno.py " + file_path, shell=True)
        """if not p.returncode:
            return static_file('p_graph.html', root='./')
        else:
            return "Код ошибки запуска модели " + str(p.returncode)"""
        return json.dumps(p)
        #print(files.get('upload'))
        #return dyno.main(files.get('upload')[0])


    def put(self, course_id):
        pass


api.add_resource(Main, "/api/")
api.init_app(app)

if __name__ == "__main__":
    app.run(debug=True, host="127.0.0.1", port=3000)



