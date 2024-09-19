FROM python:3.11

ADD . /app

WORKDIR /app
RUN python -m pip install --upgrade pip
RUN pip install --trusted-host pypi.python.org -r requirements.txt

EXPOSE 80

CMD [ "python", "server_dyno_bottle.py" ]