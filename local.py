import json
import os
import codecs
import requests

fileObj = codecs.open('mytry.bpmn', "r", "utf_8_sig")
file = fileObj.readlines()
files = {'file': file}
url = "http://127.0.0.1:3000/api/"
print(file)
res = requests.post(url, files=files) #обращение к серверу, пока что локальный
fileObj.close()
res.text
print(res)

