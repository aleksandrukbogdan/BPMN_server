import subprocess
import os

from bottle import route, run, static_file, request, hook


# СТАТИКА CSS
@route('/gantt/css/<filename>')
def server_static(filename):
    return static_file(filename, root='./gantt/css/')

# СТАТИКА JS
@route('/gantt/js/<filename>')
def server_static(filename):
    return static_file(filename, root='./gantt/js/')


# ТЕСТОВЫЙ ЗАПУСК МОДЕЛИ ФАЙЛОМ
@route('/test')
def test():
    # file = 'Res3_DiagramDelivery(Reserve).bpmn'
    subprocess.run("python dyno.py Res3_DiagramDelivery(Reserve).bpmn", shell=True)
    return static_file('p_graph.html', root='./')


# ФОРМА ЗАГРУЗКИ и ЗАПУСКА
@route('/')
def index():
    return static_file('upload.html', root='./')

# ЗАГРУЗКА и ЗАПУСК
@route('/upload', method='POST')
def do_upload():
    upload = request.files.get('upload')
    name, ext = os.path.splitext(upload.filename)
    if ext not in ('.bpmn', '.json'):
        return "File extension not allowed."

    save_path = "/tmp"
    if not os.path.exists(save_path):
        os.makedirs(save_path)

    file_path = "{path}/{file}".format(path=save_path, file=upload.filename)
    upload.save(file_path, overwrite=True)
    #return "File successfully saved to '{0}'.".format(save_path)
    p = subprocess.run("python dyno.py " + file_path, shell=True)
    if not p.returncode:
        return static_file('p_graph.html', root='./')
    else:
        return "Код ошибки запуска модели " + str(p.returncode)
    
    

run(host='localhost', port=8080)