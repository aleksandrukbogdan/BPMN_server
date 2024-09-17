# -*- coding: utf-8 -*-

"""
Created on 23.03.2012
Refactored on 17.11.2022

@author: Semyon Potryasaev, Dmitriy Pavlov
"""

# TODO: Считаем рандомом (SIMPLE_DECISION = True) если показатель FIFO лучше, чем PULP, то
# делаем SIMPLE_DECISION = False и работаем по ограниченному времени.
# Если время кончилось, а расчеты не завершены, то выдаем FIFO с ЗАПРЕТОМ! (так и происходит)

# TODO: ПРИНИМАТЬ РЕШЕНИЕ НЕ ПО ГОЛОМУ РАНДОМУ, А ПО НАПРАВЛЕННОМУ ПОИСКУ

# !!!TODO: В ИТОГЕ: ОСТАВИТЬ ВСЕ КАК ЕСТЬ, НО ИЗМЕНИТЬ РАНДОМ НА НАПРАВЛЕННЫЙ РАНДОМ И ДОБАВИТЬ ОТСЕЧКУ ПО ВРЕМЕНИ РАСЧЕТОВ
# ПРОДАКШН: SIMPLE_DESICION (ОТСЕЧКА + КРУТОЙ РАНДОМ)
# ИССЛЕДОВАНИЯ: НЕ SIMPLE_DESICION
# ВЫТАЩИТЬ ПРИОРИТЕТ ОПЕРАЦИИ ИЗ PRIORITY И ЮЗАТЬ В КАЧЕСТВЕ ВЕСА
# ПЕРВАЯ РАНДОМНАЯ ОПЕРАЦИЯ - ЖАДНАЯ. А ПОТОМ РАНДОМИТЬ С ВЕСАМИ. ЕСЛИ БУДЕТ ЛУЧШЕ, ТО ОК
# ВЕСА - ИЗ СОВОКУПНОГО ПОКАЗАТЕЛЯ

import os
import sys
import operator
from math import log10, ceil, inf
from random import randrange
from time import time
from datetime import timedelta, datetime
from itertools import groupby
from uuid import uuid1
from copy import deepcopy
from functools import reduce
import yaml
import inspect
import csv
import json

import networkx as nx
from lxml import etree  # http://www.lfd.uci.edu/~gohlke/pythonlibs/
import pulp
from pulp import LpProblem, LpMaximize, LpVariable, LpInteger, LpContinuous, lpDot, LpStatus, value
import click  # CLI



# from constants import *     # Загрузка констант из переменных среды или по умолчанию

insp = {}
i = 0
# Для записи в csv приоритетов операций

import os
import shutil

QltTemplate = {
    "J0": [1],
    "J1": [0],
    "J2": [0.5],
    "J3": [0],
    "J4": [0],
    "J5": [0],
    "J6": [0],
    "J7": [0.5],
    "J8": [0],
    "J9": [0]
}

dir_name_ID = 'zakharov_ID'
template_file = os.path.join(dir_name_ID, 'Qlt.json')
if not os.path.exists(dir_name_ID):
    os.makedirs(dir_name_ID)
    with open(template_file, 'w') as f:
        json.dump(QltTemplate, f)

# папка перезаписывается
dir_name = 'zakharov_RESULT'
if os.path.exists(dir_name):
    shutil.rmtree(dir_name)
os.makedirs(dir_name)

index_ham = 0
ham_file = open(os.path.join(dir_name, 'hamiltonian_1.csv'), 'w')
csv_data = [['time', 'Job', 'Res', 'C', 'solution']]
time_pred = 1
ham_file.close()

# Константы (для тестирования)
DEBUG = False
DEBUG_L1 = False
DEBUG_L2 = False
DEBUG_Q = False
DEBUG_FRONT = False
DEBUG_PULP = False
DEBUG_INTERRUPT = False
DEBUG_EXEC = False
DEBUG_NORMALIZE = False
DEBUG_GRAPH = False
DEBUG_TRANS = False
DEBUG_REV = False
PRINT = False
DEBUG_CTRL = False

WRITE_FILE = False

SIMPLE_DECISION = True

NORMALIZE_LOG_OP = False
NORMALIZE_LOG_ST = False
NORMALIZE_LOG_ANGLE = True

FILE_RESULT_GANT = False
FILE_RESULT_LIST = False
FILE_RESULT_CHART = False

HAMILTONIAN_THINNING: 2

# отрисовка диаграмм Ганта
PLOT_GANT = True

# DEPRECATED флаг завершения операции
NOT_COMPLETED = 0  # не завершена
TIME_COMPLETED = 1  # время вышло, поток ещё не обработан
STREAM_COMPLETED = 2  # поток обработан, время ещё осталось
FULL_COMPLETED = 3  # полностью завершена

# статус операции
OP_WAIT = 0  # ждёт начала выполнения
OP_EXEC = 1  # выполняется
OP_FLOW_COMPLETED = 2  # завершена до отведённого времени
OP_COMPLETED = 3  # завершена, отведённое время исчерпано
OP_TIMEOUT = -1  # не выполнилась до конца отведённого времени
OP_STRANGE = -2  # странный статус, возможна ошибка

# флаг постановки операции на ресурс
RES_PROCESSING = -1  # операция [может быть] запущена на выполнение
RES_REJECTED = -2  # выполнение операции отклонено ресурсом
# операция [может быть] запущена на выполнение, но полностью занимает ресурс
RES_TO_FULL = -3


class GrandSolver(object):
    """Главный класс оптимизатора плана. Контейнер модели."""

    def __init__(self, sname):
        # pydevd.settrace('macmini')

        self.p = None  # Communication Pipe для взаимодействия с порождающим процессом
        self.logger = None  # Communication Pipe для взаимодействия с порождающим процессом
        self.Name = sname  # имя модели
        self.D = 1  # интервал планирования
        self.Step = 1  # шаг планирования - фактически это качество (временнОе разрешение) исходных данных.
        # Реально в алгоритме может быть выбран другой шаг, его увеличение приведёт к быстрым расчётам
        # за счёт увеличения ошибки, уменьшение шага ниже значения Step приведёт
        # к большому времени расчёта без улучшения результата
        # TODO	отказаться от использования постоянного шага, перейти к переменному
        self.time = 0  # текущее время модели
        self.conflict_count = 0  # количество прерываний операций

        # Применяются словари для удобной работы со сквозными индексами
        self.ProcList = {}  # Словарь процессов, хранящих словари операций
        self.ClustList = {}  # Словарь кластеров, хранящих словари ресурсов
        self.Precision = 0.01  # Точность сравнения показателей качества на итерациях
        self.StructMatrix = {}  # Структурная матрица, задаёт Theta ikj: возможность выполнения операции на ресурсе

        # self.availability - Матрица потенциала доступности операций: [op_id] = [(startTime, 0/1), ...]
        # - доступность операции op_id в промежуток времени от startTime до следующего значения
        self.availability = {}

        # self.penalty - Матрица штрафных функций операций: [op_id] = [(startTime, penalty)]
        # - штраф за выполнение операции op_id с момента времени startTime и значением. Ступенчатая функция
        self.penalty = {}

        # self.res_availability - Матрица потенциала доступности ресурса: [res_id] = [(startTime, 0/1), ...]
        # - доступность ресурса res_id в промежуток времени от startTime до следующего значения
        self.res_availability = {}

        # Матрица запретов на выполнение операции: [op_id] = [(startTime, 0/1), ...]
        # - доступность операции op_id в промежуток времени от startTime до следующего значения
        self.restriction = {}

        # Список показателей качества. Содержит списки {"J#": [коэффициент, ...значения на каждой итерации, ...]).
        # J0 - обобщённый показатель качества
        # J1 - невязка по времени выполнения
        # J2 - невязка по потоку
        # J3 - качество выполнения операций (𝜂-функция)
        # J4 - штрафы за нарушения директивных сроков (q-функция)
        # J5 - неравномерность загрузки ресурсов
        # J6 - разрывность операций
        # J7 - количество завершённых процессов
        # J8 - количество завершённых операций
        # J9 - показатель робастности
        self.QltList = {
            "J0": [1],
            "J1": [0],
            "J2": [0.5],
            "J3": [0],
            "J4": [0],
            "J5": [0],
            "J6": [0],
            "J7": [0.5],
            "J8": [0],
            "J9": [0]
        }
        if os.path.exists(template_file):
            with open(template_file) as file:
                self.QltList = json.load(file)

        # Число клонов модели, которые необходимо создать при планировании
        self.Threads = None

        # Условия трансверсальности
        self.operation_conditions = dict()
        self.stream_conditions = dict()
        self.resource_conditions = dict()

        # Начальные условия сопряжённой системы
        self.operation_init_conditions = dict()
        self.stream_init_conditions = dict()
        self.resource_init_conditions = dict()

        self.OpPriorMatrix = {}  # Список приоритетов операций [операция] = приоритет
        self.ResPriorMatrix = {}  # Список приоритетов ресурсов [ресурс] = приоритет
        self.StreamPriorMatrix = {}  # Список потоковых приоритетов операций [операция] = потоковый приоритет

        # Список максимальных интенсивностей выполнения операций ресурсами [(операция, ресурс)] = (startTime, intens)
        #  - интенсивность ресурса Res для операции op в промежуток времени от startTime до следующего значения
        self.ProductivityMatrix = {}

        # хранение расписания:
        # [{(время, операция)}] = (ресурс, интенсивность) - лист словарей с индексами-кортежами
        self.timetable = []

        # хранение итогового расписания: {(процесс, операция)} = [{'start', 'stop', 'res', 'intens'}]
        self.Schedule = {}

        self.debug_vars = {}

        # DOPS (PDA)
        self.Priorities_all = {}


    def read_xml(self, model_filename=None, model_str=None):
        """Создание модели по файлу XML.
        Аргумент:
        :param model_filename: относительный путь к файлу модели.
        """

        dyn = GrandSolver(os.path.split(model_filename)[-1] if model_filename else "Неизвестный xml")

        if model_filename:
            tree = etree.parse(model_filename)
            root = tree.getroot()
        elif model_str:
            root = etree.fromstring(model_str)
        else:
            raise Exception('No file-xml or xml-str model')

        dyn.D = float(root.find("duration").text)
        # dyn.Name = root.find("name").text
        th = root.find("threads")
        try:
            dyn.Threads = int(th.text)
        except:
            dyn.Threads = None

        # коэффициенты частных показателей качества в скалярной свёртке
        coefs = root.find("coefficients")
        dyn.QltList["J0"][0] = 1  # "Неполнота выполнения операций"
        dyn.QltList["J1"][0] = float(coefs.find(
            "integrity").text.replace(",", "."))
        dyn.QltList["J2"][0] = float(coefs.find("flow").text.replace(
            ',', '.'))  # "Неполнота обработки потока"
        dyn.QltList["J3"][0] = float(coefs.find("cost").text.replace(
            ',', '.'))  # Стоимость реализации плана
        dyn.QltList["J4"][0] = float(coefs.find(
            "fine").text.replace(',', '.'))  # "Директивные сроки"
        dyn.QltList["J5"][0] = float(coefs.find("uniform").text.replace(
            ',', '.'))  # "Неравномерность загруженности ресурсов"
        dyn.QltList["J6"][0] = float(coefs.find(
            "interrupt").text.replace(',', '.'))  # Конфликтность
        dyn.QltList["J7"][0] = float(coefs.find("time").text.replace(',', '.'))
        dyn.QltList["J8"][0] = 0
        dyn.QltList["J9"][0] = 0

        # построение списка процессов
        for procelement in root.iter("process"):
            tempproc = dyn.AddProc(procelement.findtext(
                "name"), procelement.findtext("id"))
            # if dyn.p: dyn.p.send("INF: Загрузка процесса " + str(tempproc.ID))

            # # заполнение врЕменной матрицы потенциалов доступности процесса
            # process_availability = []
            #
            # avail_element = procelement.find("availability")
            # if avail_element is not None:
            #     for val in avail_element.iter("value"):
            #         process_availability.append((float(val.attrib["time"]), int(val.text)))

            # добавление операций в процесс
            # previousop = None
            for opelement in procelement.iterfind("operation"):
                new_operation = tempproc.add_operation(opelement.findtext("name"),
                                                       float(opelement.findtext(
                                                           "volume").replace(',', '.')),
                                                       opelement.findtext(
                                                           "stream"),
                                                       opelement.findtext("id"),
                                                       opelement.findtext("id"),
                                                       # opelement.findtext("template_id"),
                                                       opelement.findtext("x"),
                                                       opelement.findtext("y"))

                # копируем матрицу потенциала доступности из процесса в операцию
                # dyn.availability[new_operation.ID] = list(process_availability)
                # заполнение врЕменной матрицы потенциалов доступности процесса
                op_availability = []

                avail_element = opelement.find("availability")
                if avail_element is not None:
                    for val in avail_element.iter("value"):
                        op_availability.append(
                            (float(val.attrib["time"]), int(val.text)))
                    op_availability.insert(0, (0, 0))
                dyn.availability[new_operation.ID] = op_availability[:]

                # заполнение штрафной матрицы
                op_penalty = ()

                penalty_element = opelement.find("penalty")
                if penalty_element is not None:
                    op_penalty = ((float(penalty_element.findtext("start").replace(',', '.')),
                                   float(penalty_element.findtext("angle").replace(',', '.')), 0))
                    dyn.penalty[new_operation.ID] = op_penalty

            # построение графа операций
            graph_element = procelement.find("graph")
            if graph_element is not None:
                for edge in procelement.find("graph").iter("edge"):
                    tempproc.add_link(edge.attrib["from"], edge.attrib["to"],
                                      edge.findtext("fwd") if edge.find(
                                          "fwd") is not None else 1,
                                      edge.findtext("rev") if edge.find("rev") is not None else 1)

        # построение списка кластеров и ресурсов
        # if dyn.p: dyn.p.send("INF: Загрузка ресурсов")
        for clustelement in root.iterfind("cluster"):
            tempclust = dyn.AddClust(clustelement.findtext("name"))
            for reselement in clustelement.iter("resource"):
                tempres = tempclust.AddRes(reselement.find("name").text,
                                           float(reselement.findtext(
                                               "power").replace(',', '.')),
                                           reselement.findtext(
                                               "capacity"), reselement.findtext("price"),
                                           reselement.findtext("id"),
                                           reselement.findtext("template_id"))
                avail_element = reselement.find("availability")
                res_availability = []
                if avail_element is not None:
                    for val in avail_element.iter("value"):
                        res_availability.append(
                            (float(val.attrib["time"]), int(val.text)))

                dyn.res_availability[tempres.ID] = list(res_availability)

        # заполнение матрицы производительности ресурсов при обслуживании каждого вида операций

        for resprod in root.find("productivity").iter("resource"):
            for opprod in resprod.iter("job"):
                dyn.ProductivityMatrix[(opprod.attrib["ID"], resprod.attrib["ID"])] = float(
                    opprod.findtext("value"))

        # PAVLOV: + number of threads from XML (max of jobs list)
        dyn.Threads = dyn.Threads or len(dyn.ProductivityMatrix)

        return dyn

    def read_bpmn(self, bpmn_file):

        if not os.path.isfile(bpmn_file):
            print("это не файл!!!!! падаю с ошибкой в def read_bpmn")
            if os.path.exists(bpmn_file):
                print("Path exists")
            else:
                print("Path does not exist")
            exit(1)
        dyn = GrandSolver(os.path.split(bpmn_file)[-1])

        if DEBUG:
            print("Создание модели по файлу BPMN")

        tree = etree.parse(bpmn_file)
        root = tree.getroot()

        # get its namespace map, excluding default namespace
        nsmap = {
            "mdl": "http://www.omg.org/spec/BPMN/20100524/MODEL",
            "ltsm": "http://litsam.ru",
            "bpmndi": "http://www.omg.org/spec/BPMN/20100524/DI",
            "dc": "http://www.omg.org/spec/DD/20100524/DC"
        }

        # построение ресурсов

        if DEBUG:
            print("Добавление ресурсов")

        clstr = dyn.AddClust("Пул ресурсов")
        for reselement in root.iterfind("mdl:resource", nsmap):
            res_threads = reselement.xpath("mdl:extensionElements/ltsm:props[@name='threads']/@value",
                                           namespaces=nsmap) or [None]
            res_price = reselement.xpath("mdl:extensionElements/ltsm:props[@name='price']/@value",
                                         namespaces=nsmap) or [None]
            res_productivity = reselement.xpath("mdl:extensionElements/ltsm:props[@name='productivity']/@value",
                                                namespaces=nsmap) or [None]
            tempres = clstr.AddRes(reselement.attrib.get("name"), res_productivity[0], res_threads[0], res_price[0],
                                   reselement.attrib.get("id"), uuid1())
            if DEBUG:
                print("\t" + tempres.Name)

            ##!~ Palich
            res_availability = []
            res_avail_element_times = reselement.xpath("mdl:extensionElements/ltsm:availability/@availability_time",
                                                       namespaces=nsmap) or None
            res_avail_element_times = res_avail_element_times or reselement.xpath(
                "mdl:extensionElements/ltsm:availability[@name='availability_time']/@value", namespaces=nsmap)
            res_avail_element_times = res_avail_element_times or None
            res_avail_element_values = reselement.xpath("mdl:extensionElements/ltsm:availability/@availability_value",
                                                        namespaces=nsmap) or None
            res_avail_element_values = res_avail_element_values or reselement.xpath(
                "mdl:extensionElements/ltsm:availability[@name='availability_value']/@value", namespaces=nsmap)
            res_avail_element_values = res_avail_element_values or None
            # print(res_avail_element_times)
            # print(res_avail_element_values)

            if res_avail_element_times is not None and res_avail_element_values is not None:
                for time_val in zip(res_avail_element_times, res_avail_element_values):
                    # print(time_val)
                    res_availability.append(
                        (float(time_val[0]), int(time_val[1])))
                res_availability.insert(0, (0, 0))
            dyn.res_availability[tempres.ID] = res_availability[:]
            # print(dyn.res_availability)
            ##!~ /Palich
            # if self.p: self.p.send("INF: Загрузка процесса " + str(tempproc.ID))
        # построение списка процессов
        # exit()
        print("Добавление процессов")

        # ОСТАЛОСЬ в bpmn_reader.py
        # global temp_coords
        # temp_coords.clear()

        for procelement in root.iterfind("mdl:process", nsmap):
            tempproc = dyn.AddProc(procelement.attrib.get("id"))
            print("\t" + tempproc.Name)
            # if self.p: self.p.send("INF: Загрузка процесса " + str(tempproc.ID))

            # добавление операций в процесс

            print("\tДобавление операций")

            for opelement in procelement.iterfind("mdl:task", nsmap):
                templ = opelement.find("mdl:extensionElements", nsmap)
                #ttt = templ.find("ltsm:props", nsmap)
                #ttt = templ.getchildren()
                # templ_uuid = templ.find("ctss:template_id", nsmap)
                templ_uuid = None

                # Оба способа чтения (added by Palich)
                op_volume = opelement.xpath("mdl:extensionElements/ltsm:props/@volume", namespaces=nsmap) or None
                op_volume = op_volume or opelement.xpath("mdl:extensionElements/ltsm:props[@name='volume']/@value",
                                                         namespaces=nsmap)
                op_volume = op_volume or ["0"]
                op_stream = opelement.xpath("mdl:extensionElements/ltsm:props/@stream", namespaces=nsmap) or None
                op_stream = op_stream or opelement.xpath("mdl:extensionElements/ltsm:props[@name='stream']/@value",
                                                         namespaces=nsmap)
                op_stream = op_stream or ["0"]
                op_penalty_start = opelement.xpath("mdl:extensionElements/ltsm:props/@penalty_start",
                                                   namespaces=nsmap) or None
                op_penalty_start = op_penalty_start or opelement.xpath(
                    "mdl:extensionElements/ltsm:props[@name='penalty_start']/@value", namespaces=nsmap)
                op_penalty_start = op_penalty_start or ["0"]
                op_penalty_angle = opelement.xpath("mdl:extensionElements/ltsm:props/@penalty_angle",
                                                   namespaces=nsmap) or None
                op_penalty_angle = op_penalty_angle or opelement.xpath(
                    "mdl:extensionElements/ltsm:props[@name='penalty_angle']/@value", namespaces=nsmap)
                op_penalty_angle = op_penalty_angle or ["0"]

                ##!~ Palich
                op_availability = []
                avail_element_times = opelement.xpath("mdl:extensionElements/ltsm:availability/@availability_time",
                                                      namespaces=nsmap) or None
                avail_element_times = avail_element_times or opelement.xpath(
                    "mdl:extensionElements/ltsm:availability[@name='availability_time']/@value", namespaces=nsmap)
                avail_element_times = avail_element_times or None
                avail_element_values = opelement.xpath("mdl:extensionElements/ltsm:availability/@availability_value",
                                                       namespaces=nsmap) or None
                avail_element_values = avail_element_values or opelement.xpath(
                    "mdl:extensionElements/ltsm:availability[@name='availability_value']/@value", namespaces=nsmap)
                avail_element_values = avail_element_values or None
                # print(avail_element_times)
                # print(avail_element_values)

                if avail_element_times is not None and avail_element_values is not None:
                    for time_val in zip(avail_element_times, avail_element_values):
                        # print(time_val)
                        op_availability.append(
                            (float(time_val[0]), int(time_val[1])))
                    op_availability.insert(0, (0, 0))
                ##!~ /Palich

                # op_volume = opelement.xpath("mdl:extensionElements/ltsm:props[@name='volume']/@value", namespaces=nsmap) or [""]
                # op_stream = opelement.xpath("mdl:extensionElements/ltsm:props[@name='stream']/@value", namespaces=nsmap) or [""]

                for dc in root.iterfind("bpmndi:BPMNDiagram", nsmap):
                    op_x = dc.xpath("bpmndi:BPMNPlane/bpmndi:BPMNShape[@bpmnElement='" + opelement.attrib.get(
                        "id") + "']/dc:Bounds/@x", namespaces=nsmap)
                    op_y = dc.xpath("bpmndi:BPMNPlane/bpmndi:BPMNShape[@bpmnElement='" + opelement.attrib.get(
                        "id") + "']/dc:Bounds/@y", namespaces=nsmap)
                    # temp_coords[opelement.attrib.get("id")] = {"x": op_x and op_x[0], "y": op_y and op_y[0]}

                # идентификаторы операций генерируются в UUID виде, если не были заданы
                tempop = tempproc.add_operation(opelement.attrib.get("name"), op_volume[0].replace(',', '.'),
                                                op_stream[0].replace(',', '.'), opelement.attrib.get("id"),
                                                templ_uuid.text if templ_uuid is not None else uuid1())
                if DEBUG:
                    print("\t\t" + tempop.ID, tempop.Name, tempop.A, tempop.AP, end="")
                if DEBUG:
                    if opelement.find("mdl:performer", nsmap) is None:
                        print(" нет исполнителя", end=" ")
                    else:
                        print(" выполняется на:", end=" ")

                # формирование матрицы penalty
                dyn.penalty[tempop.ID] = (
                (float(op_penalty_start[0].replace(',', '.')), (float(op_penalty_angle[0].replace(',', '.'))), 0))
                # формирование матрицы availability
                dyn.availability[tempop.ID] = op_availability[:]
                # print(dyn.availability)

                # формирование матрицы продуктивности
                # изменено значение по умолчанию: если есть указание ресурса "в короткой записи", то считать продуктивность за 1.0
                # иначе зачем вообще ссылка на ресурс
                for performerelement in opelement.iterfind("mdl:performer", nsmap):
                    dyn.ProductivityMatrix[tempop.ID, performerelement.find("mdl:resourceRef", nsmap).text] = \
                        float((performerelement.xpath("mdl:resourceParameterBinding/mdl:formalExpression/text()",
                                                      namespaces=nsmap) or [1])[0])
                    if DEBUG:
                        print(performerelement.find("mdl:resourceRef", nsmap).text, end=" ")
                if DEBUG:
                    print()

            evnt = procelement.find("mdl:startEvent", nsmap)
            start_event = evnt.attrib.get("id")
            evnt = procelement.find("mdl:endEvent", nsmap)
            end_event = evnt.attrib.get("id")

            # добавление связей в процесс

            print("\tДобавление связей")

            # прямые связи операций
            print("\t\tпрямые связи")
            lnks = dict()
            for link in procelement.iterfind("mdl:sequenceFlow", nsmap):
                # если связываются операции, которые числятся в списке реальных операций модели,
                # то связываем их непосредственно
                legal_op_list = [op[1].ID for op in dyn.op_iter()]
                if link.attrib.get("sourceRef") in legal_op_list and link.attrib.get("targetRef") in legal_op_list:
                    tempproc.add_link(link.attrib.get("sourceRef"), link.attrib.get("targetRef"))
                    if DEBUG:
                        print("\t\t\t" + link.attrib.get("sourceRef") + " - " + link.attrib.get("targetRef"))
                # иначе готовимся к альтернативным связям
                elif link.attrib.get("sourceRef") not in [start_event, end_event] and link.attrib.get(
                        "targetRef") not in [start_event, end_event]:
                    lnks[link.attrib.get("id")] = {'src': link.attrib.get("sourceRef"),
                                                   'tgt': link.attrib.get("targetRef")}

            # Рассматриваем gateways и строим связи между операциями, исключая их
            # связи типа И
            print("\t\tсвязи типа И")
            pg = dict()
            for pargat in procelement.iterfind("mdl:parallelGateway", nsmap):
                if pargat.attrib.get("gatewayDirection") == 'Diverging':
                    src_op = lnks[pargat.find("mdl:incoming", nsmap).text].get('src')
                    if DEBUG:
                        print("\t\t\t" + src_op, end=" -> ")
                    grp = 1
                    for outl in pargat.iterfind("mdl:outgoing", nsmap):
                        # связи с разным grp считаются как "И"
                        tempproc.add_link(src_op, lnks[outl.text].get("tgt"), fwd_group=grp)
                        grp += 1
                        if DEBUG:
                            print(lnks[outl.text].get("tgt"), end=", ")
                    if DEBUG:
                        print()
                if pargat.attrib.get("gatewayDirection") == 'Converging':
                    dst_op = lnks[pargat.find("mdl:outgoing", nsmap).text].get('tgt')
                    grp = 1
                    for inpl in pargat.iterfind("mdl:incoming", nsmap):
                        tempproc.add_link(lnks[inpl.text].get("src"), dst_op, rev_group=grp)
                        grp += 1
                        if DEBUG:
                            print("\t\t\t" + src_op + " - " + lnks[outl.text].get("tgt"))

            # связи типа ИЛИ
            print("\t\tсвязи типа ИЛИ")
            eg = dict()
            for exgat in procelement.iterfind("mdl:exclusiveGateway", nsmap):
                if exgat.attrib.get("gatewayDirection") == 'Diverging':
                    src_op = exgat.find("mdl:incoming", nsmap).text
                    if src_op in lnks:
                        src_op = lnks[src_op].get('src')
                        if DEBUG:
                            print("\t\t\t" + src_op, end=" -> ")

                        for outl in exgat.iterfind("mdl:outgoing", nsmap):
                            tempproc.add_link(src_op, lnks[outl.text].get("tgt"))
                            if DEBUG:
                                print(lnks[outl.text].get("tgt"), end=", ")
                        if DEBUG:
                            print()

                if exgat.attrib.get("gatewayDirection") == 'Converging':
                    dst_op = exgat.find("mdl:outgoing", nsmap).text
                    if dst_op in lnks:
                        dst_op = lnks[dst_op].get('tgt')
                        if DEBUG:
                            print("\t\t\t", end="")
                        for inpl in exgat.iterfind("mdl:incoming", nsmap):
                            tempproc.add_link(lnks[inpl.text].get("src"), dst_op)
                            if DEBUG:
                                print(lnks[inpl.text].get("src"), end=", ")
                        if DEBUG:
                            print(" -> " + dst_op)
        # возвращаем сформированную по BPMN-файлу модель
        return dyn

    def res_iter(self):
        """Итератор ресурсов по всем кластерам"""
        for clust in self.ClustList.values():
            for res in clust.ResList.values():
                yield (clust, res)

    def op_iter(self):
        """Итератор операций по всем процессам.
        :return (process, operation): кортеж из процесса и операции
        """
        for proc in self.ProcList.values():
            for op in proc.OpList.values():
                yield (proc, op)

    def AddProc(self, pname, pid=None):
        "Добавление процесса в модель. Возвращает созданный процесс"
        newproc = UniProcess(pname, pid)
        self.ProcList[newproc.ID] = newproc
        return newproc

    def DelProc(self, pid):
        "Удаление процесса из модели. Операции процесса удаляются сборщиком мусора Python"
        del self.ProcList[pid]

    def get_proc(self, proc_id):
        "Получение процесса по его идентификатору"
        return self.ProcList[proc_id]

    def get_proc_op(self, op_id):
        "Получения пары (процесс, операция) по идентификатору операции"
        for proc in self.ProcList.values():
            if op_id in proc.OpList:
                return (proc, proc.OpList[op_id])

    def set_restriction(self, op_id, ts=None, tf=None):
        """Установка врЕменного запрета на выполнение операции.
        :param op_id: идентификатор операции
        :param ts: время начала запретного периода
        :param tf: время окончания запретного периода
        """

        def merge_intervals(intervals):
            """
            A simple algorithm can be used:
            1. Sort the intervals in increasing order
            2. Push the first interval on the stack
            3. Iterate through intervals and for each one compare current interval
               with the top of the stack and:
               A. If current interval does not overlap, push on to stack
               B. If current interval does overlap, merge both intervals in to one
                  and push on to stack
            4. At the end return stack
            """
            sorted_by_lower_bound = sorted(intervals, key=lambda tup: tup[0])
            merged = []

            for higher in sorted_by_lower_bound:
                if not merged:
                    merged.append(higher)
                else:
                    lower = merged[-1]
                    # test for intersection between lower and higher:
                    # we know via sorting that lower[0] <= higher[0]
                    if higher[0] <= lower[1]:
                        upper_bound = max(lower[1], higher[1])
                        merged[-1] = (lower[0], upper_bound)  # replace by merged interval
                    else:
                        merged.append(higher)
            return merged

        if op_id in self.restriction:

            if ts is not None and tf is not None:
                a = self.restriction[op_id][:]
                a.append((ts, tf))
                self.restriction[op_id] = merge_intervals(a)
            else:
                del self.restriction[op_id]
        else:
            if ts is not None and tf is not None:
                self.restriction[op_id] = [(ts, tf)]

    def get_availability(self, op_id, time):
        """Получение значения доступности операции в заданное время.
        Проверка с учётом запретов для ликвидации прерываний. Лист моментов времени должен быть сортирован.
        :param op_id: идентификатор операции
        :param time: время проверки доступности
        :return: 1 если операция доступна, 0 - если нет
        """
        availability_result = 1  # если нет сведений о доступности, считать, что операция доступна всегда
        restriction_result = 1  # если нет сведений о запрете на выполнение, считать, что запрета нет
        for t, a in self.availability.get(op_id, []):
            if time >= t:
                availability_result = a
        for t in self.restriction.get(op_id, []):
            if time >= t[0] and time < t[1]:
                restriction_result = 0
            else:
                restriction_result = 1

        return availability_result * restriction_result

    def get_penalty(self, op_id, time):
        """
        DEPRECATED
        Получение значения штрафа операции в заданное время.
        :param op_id: идентификатор операции
        :param time: время проверки доступности
        :return: значение функции штрафа
        """

        if not self.penalty.get(op_id, False):
            return 0

        (startTime, angle, fine) = self.penalty[op_id]

        penalty_result = angle if time > startTime else 0

        return penalty_result

    def get_res_availability(self, res_id, time):
        """Получение значения доступности ресурса в заданное время.
        Лист моментов времени должен быть сортирован.
        :param res_id: идентификатор операции
        :param time: время проверки доступности
        :return: 1 если операция доступна, 0 - если нет
        """
        availability_result = 1  # если нет сведений о доступности, считать, что ресурс доступен всегда
        for t, a in self.res_availability.get(res_id, []):
            if time >= t:
                availability_result = a

        return availability_result

    def get_clust(self, clust_id):
        "Получения кластера по идентификатору"
        return self.ClustList[clust_id]

    def get_clust_res(self, res_id):
        """
        Получения пары (кластер, ресурс) по идентификатору ресурса
        :param res_id:
        :return: кортеж (кластер, ресурс)
        """
        for clust in self.ClustList.values():
            if res_id in clust.ResList:
                return (clust, clust.ResList[res_id])

    def AddClust(self, cname, bandw=0, cid=None):
        "Добавление кластера в модель. Возвращает созданный кластер"
        newclust = UniClust(cname, bandw, cid)
        self.ClustList[newclust.ID] = newclust
        return newclust

    def DelClust(self, cid):
        "Удаление кластера из модели"
        del self.ClustList[cid]

    def get_productivity(self, op_id, res_id):
        "Определение продуктивности выполнения операции op на ресурсе res"

        # OLD CODE
        #		prod = 0 # принимаем по умолчанию, что ресурс недоступен для операции
        # 		for trigger, val in self.ProductivityMatrix[(op, res)]:
        # 			#print (trigger, val)
        # 			if t > trigger: prod = val
        # 		return prod
        # END OF OLD
        return self.ProductivityMatrix.get((op_id, res_id), 0)

    def calculate_priorities(self, t=None):
        """Расчёт значений сопряжённых переменных (приоритетов операций) и вспомогательных значений
        на текущий или заданный момент времени.
        Внимание! Ведётся расчёт одного шага, а не суммирование по всему интервалу времени.
        :param t: Заданный момент времени. Если не указан, расчёт ведётся на текущее время модели self.time
        """
        if DEBUG_L2:
            print("Расчёт значений сопряжённых переменных (приоритетов)")

        if t is None:
            t = self.time

        # для каждого процесса
        for proc_prior in self.ProcList.values():
            if DEBUG_L2:
                print("\tПроцесс", proc_prior.Name)
            # проходим по вершинам графа
            for n in proc_prior.graph.nodes():
                if DEBUG_L2:
                    print("\t\tОперация", self.get_proc_op(n)[1].Name)

                # Флаг выполнения текущей операции
                op_exec_flag = True if self.timetable[-1].get((t, n), False) else False

                # Если операция выполняется за пределами директивного срока - оштрафовать её
                if op_exec_flag and len(self.penalty.get(n, [])) != 0 and t >= self.penalty[n][0]:
                    # PDA: заменен неправильный механизм оштрафования операции по вревышению директивного срока (штрафуем на величину angle: fine, который идет в показатель J4 становится равным angle)
                    # self.penalty[n] = self.penalty[n][1]
                    self.penalty[n] = (self.penalty[n][0], self.penalty[n][1], self.penalty[n][1])
                # Основная модель: сумма коэффициентов по предшественникам + сумма коэффициентов по параллельным

                summa_pred = 0
                summa_parallel = 0

                # для выбранной вершины проходим по предшествующим работам
                for pred_op_id in proc_prior.graph.predecessors(n):

                    # просматриваем все ресурсы
                    for (clust, res) in self.res_iter():
                        # суммирование (Основное управление * множитель Лагранжа sigma_i_kappa_wave)

                        # если нужно компенсировать уход в отрицательную область, то использовать эту строку:
                        # summa = max(float("2"), summa - (1 if res.ID ==

                        # включаем единицу, если предыдущая работа выполняется в текущий момент времени
                        # и прибавляем текущей работе приоритет предыдущей
                        summa_pred += (1 if res.ID == self.timetable[-1].get((t, pred_op_id), (-1, -1))[0] else 0) * \
                                      (
                                          # основной приоритет * epsilon * theta
                                          # epsilon и theta гарантировано равны 1, так как включено управление
                                              self.OpPriorMatrix.get(pred_op_id,
                                                                     self.operation_init_conditions.get(pred_op_id,
                                                                                                        0)) +
                                              # ресурсный приоритет
                                              self.ResPriorMatrix.get(res.ID,
                                                                      self.resource_init_conditions.get(res.ID, 0)) +
                                              # матрицу eta имитирует продуктивность - будем выбирать ресурс с меньшей стоимостью
                                              # self.get_productivity(pred_op_id, res.ID) -
                                              # штрафы
                                              self.get_penalty(pred_op_id, t) +
                                              # потоковый приоритет * макс. производительность
                                              self.StreamPriorMatrix.get(pred_op_id,
                                                                         self.stream_init_conditions.get(pred_op_id,
                                                                                                         0)) *
                                              self.get_productivity(pred_op_id, res.ID)
                                      )
                        if DEBUG_L2 and (res.ID == self.timetable[-1].get((t, pred_op_id), (-1, -1))[0]):
                            print("\t\t\tРаботает", self.get_proc_op(pred_op_id)[1].Name)

                    # учёт параллельно выполняемых операций (исключающее или)
                    # TODO изучить ошибку двойного учёта параллельных операций при нескольких предшественниках

                    for s in proc_prior.graph.successors(pred_op_id):
                        # для каждого предшественника пройти по всем последователям -
                        # так формируется список параллельно выполняемых операций
                        if s == n:
                            continue
                        if proc_prior.graph.edges[pred_op_id, s]['fwd'] == proc_prior.graph.edges[pred_op_id, n]['fwd']:
                            # группа 'fwd' соседней дуги совпадает с 'fwd' текущей дуги, что означает альтернативное или
                            for (clust, res) in self.res_iter():
                                # суммирование (Основное управление * множитель Лагранжа 𝜎_𝑖𝜘~)

                                # если нужно компенсировать уход в отрицательную область, то использовать эту строку:
                                # summa = max(float("2"), summa -
                                # включаем единицу, если предыдущая работа выполняется в текущий момент времени
                                # и прибавляем текущей работе приоритет предыдущей
                                summa_parallel += (1 if res.ID == self.timetable[-1].get((t, s), (-1, -1))[0] else 0) * \
                                                  (
                                                      # основной приоритет * epsilon * theta
                                                      # epsilon и theta гарантировано равны 1, так как включено управление
                                                          self.OpPriorMatrix.get(s,
                                                                                 self.operation_init_conditions.get(s,
                                                                                                                    0)) +
                                                          # ресурсный приоритет
                                                          self.ResPriorMatrix.get(res.ID,
                                                                                  self.resource_init_conditions.get(
                                                                                      res.ID, 0)) +
                                                          # матрицу eta имитирует продуктивность - будем выбирать ресурс с меньшей стоимостью
                                                          # self.get_productivity(pred_op_id, res.ID) -
                                                          # штрафы
                                                          self.get_penalty(pred_op_id, t) +
                                                          # потоковый приоритет * макс. производительность
                                                          self.StreamPriorMatrix.get(s,
                                                                                     self.stream_init_conditions.get(s,
                                                                                                                     0)) *
                                                          self.get_productivity(s, res.ID)
                                                  )

                                # 					for succ_op_id in proc_prior.graph.successors_iter(n):
                                # 						for (clust,res) in self.res_iter():
                                # 							summa = summa - (self.OpPriorMatrix[succ_op_id] if
                                # self.timetable[len(self.timetable)-1].get((t,succ_op_id), (-1, -1))[0] == res.ID
                                # else 0)

                # слагаемое с вспомогательной переменной "p"
                if DEBUG and False:
                    print()
                    print(1 if self.get_proc_op(n)[1].Status == OP_COMPLETED else 0)

                # берём начальное значение из матрицы приоритетов или начальных условий

                if NORMALIZE_LOG_ANGLE and (summa_pred + summa_parallel) > 1:
                    self.OpPriorMatrix[n] = self.OpPriorMatrix.get(n, self.operation_init_conditions.get(n, 0)) + \
                                            log10(summa_pred + summa_parallel)
                    if DEBUG_NORMALIZE:
                        print("Нормализовано 𝜓º", self.OpPriorMatrix.get(n, self.operation_init_conditions.get(n, 0)) +
                              summa_pred + summa_parallel, self.OpPriorMatrix[n])
                else:
                    self.OpPriorMatrix[n] = self.OpPriorMatrix.get(n, self.operation_init_conditions.get(n, 0)) + \
                                            summa_pred + summa_parallel

                if DEBUG_L2:
                    print("\t\t\t𝜓º:", self.OpPriorMatrix[n], "(", summa_pred, summa_parallel, ")")

                # Потоковая модель:

                # берём начальное значение из матрицы приоритетов или начальных условий
                # self.StreamPriorMatrix.get(n, self.stream_init_conditions.get(n, 0))
                sum_stream = 0  # сумма по операциям-последователям "И", "Альтернативное ИЛИ"

                # суммируем по всем ресурсам
                for (clust, res) in self.res_iter():
                    # операции - последователи
                    for succ_op_id in proc_prior.graph.successors(n):
                        # если нужно компенсировать уход в отрицательную область, то использовать эту строку:
                        # sum_stream = max(2, sum_stream - (self.OpPriorMatrix[succ_op_id] if
                        sum_stream = (sum_stream +
                                      # (self.OpPriorMatrix[succ_op_id] if
                                      #             self.timetable[len(self.timetable) - 1].get(
                                      #                 (t, succ_op_id), (-1, -1))[0] == res.ID else 0)
                                      (1 if res.ID == self.timetable[-1].get((t, succ_op_id), (-1, -1))[0] else 0) *
                                      # включаем единицу, если предыдущая работа выполняется в текущий момент времени
                                      # и прибавляем текущей работе приоритет предыдущей
                                      (
                                          # основной приоритет * epsilon * theta
                                          # epsilon и theta гарантировано равны 1, так как включено управление
                                              self.OpPriorMatrix.get(succ_op_id,
                                                                     self.operation_init_conditions.get(succ_op_id,
                                                                                                        0)) +
                                              # ресурсный приоритет
                                              self.ResPriorMatrix.get(res.ID,
                                                                      self.resource_init_conditions.get(res.ID, 0)) +
                                              # TODO добавить матрицы eta, q
                                              #  eta - q +
                                              # потоковый приоритет * макс. производительность
                                              self.StreamPriorMatrix.get(succ_op_id,
                                                                         self.stream_init_conditions.get(succ_op_id,
                                                                                                         0)) *
                                              self.get_productivity(succ_op_id, res.ID)
                                      )
                                      )

                # sum начинаются с 0, прибавляем предыдущее значение
                if NORMALIZE_LOG_ANGLE and (self.StreamPriorMatrix.get(n, self.stream_init_conditions.get(n, 0)) - \
                                            sum_stream) > 1:
                    self.StreamPriorMatrix[n] = log10(
                        self.StreamPriorMatrix.get(n, self.stream_init_conditions.get(n, 0)) - \
                        sum_stream)
                    if DEBUG_NORMALIZE:
                        print("Нормализовано 𝜓ⁿ",
                              self.StreamPriorMatrix.get(n, self.stream_init_conditions.get(n, 0)) - \
                              sum_stream, self.StreamPriorMatrix[n])

                else:
                    self.StreamPriorMatrix[n] = self.StreamPriorMatrix.get(n, self.stream_init_conditions.get(n, 0)) - \
                                                sum_stream
                    # - sum_stream_p перенесено в основное управление

                if DEBUG_L2:
                    print("\t\t\t𝜓ⁿ:", self.StreamPriorMatrix[n])

                if DEBUG_L2:
                    print()

                if DEBUG_CTRL:
                    self.ograph[n].append(self.OpPriorMatrix[n])
                    self.pgraph[n].append(self.StreamPriorMatrix[n])
                    # пишем последнюю цифру ID ресурса или underscore
                    # self.work[n].append(string.ascii_lowercase[int(self.timetable[-1][(t, n)][0][3:])] if (t, n) in self.timetable[-1] else
                    self.work[n].append(self.timetable[-1][(t, n)][0][3:] if (t, n) in self.timetable[-1] else
                                        ('_' if self.get_availability(n, t) else ' '))

        # Ресурсная модель: не изменяется
        if DEBUG_L2:
            print("\tПриоритеты ресурсов:", end=" ")

        for (clust, res) in self.res_iter():
            self.ResPriorMatrix[res.ID] = self.ResPriorMatrix.get(res.ID, self.resource_conditions.get(res.ID, 0))
            if DEBUG_L2:
                print("𝜓ᴾ[" + res.Name + "]:", self.ResPriorMatrix[res.ID], end=", ")

    def integrate(self, ts=0.0, tf=float('inf'), options=None):
        """Проход интегратора по интервалу планирования с заданным алгоритмом поиска решения.
        :param ts: время начала интервала планирования
        :param tf: время окончания интервала планирования
        :param options: параметры расчётов
                        method: алгоритм поиска решения (FIFO, LIFO, PULP, EXEC)
                        relaxed: снятие ограничений на неразрывность операций
        """
        if DEBUG_L1:
            print()
            print('*' * 60)
            print("Интегрирование в прямом направлении")

        OpFront = []  # фронт работ !!! сильно зависит от порядка элементов, не менять на словарь!
        ResFront = []  # фронт ресурсов	!!! сильно зависит от порядка элементов, не менять на словарь!
        self.Record = 0  # Показатель качества на предыдущей итерации

        if options is None:
            method = 'FIFO'
            relaxed = True
            debug_tab = 0
        else:
            method = options.get('method', 'FIFO')
            relaxed = options.get('relaxed', False)
            debug_tab = options.get('debug_tab', 0)

        if method == 'EXEC':
            croptt = {k: v for k, v in self.timetable[-1].items() if k[0] <= tf}
            self.timetable[-1] = croptt.copy()
        else:
            self.timetable.append({})  # Для работы Any Time Algorithm сохраняем расписание на каждой итерации

        if self.p:
            self.p.send("INF: Старт интегрирования " + method)

        def MakeOpFront(time):
            """Создание фронта работ в момент времени t - список всех операций,
            которые готовы выполняться в текущий момент времени:
            все предыдущие работы завершены, потенциал доступности = 1
            """

            if DEBUG_L2:
                print("Построение фронта работ")

            if self.p: self.p.send("INF: Построение фронта работ на " + str(time))
            del OpFront[:]

            # d2 = dict((key, [G[1] for G in g]) for (key, g) in groupby(sorted( (val, key) for (key, val) in d.items() ), lambda X: X[0]) )

            # for prev_op in [{n: self.graph.in_edges(n, True)} for n in self.graph.nodes_iter()]:

            # формирование фронта работ с исключающим ИЛИ:
            # для каждого узла графа входящие дуги группируются по типу 'rev_group'.
            # значения (A - X) перемножаются для одинаковых групп 'rev' (т.е. предыдущие работы)
            # и затем суммируются для разных групп
            for proc in self.ProcList.values():
                for n in proc.graph.nodes():
                    if False:
                        print(time, proc.get_op(n).Status, proc.get_op(n).Name)
                    candidate_operation = proc.get_op(n)
                    if candidate_operation.Status == OP_WAIT or candidate_operation.Status == OP_EXEC:
                        # Проверяем логические ограничения:

                        # Задача - понять, все ли предшествующие операции завершились и можно ли стартовать текущую операцию. Но с соблюдением всей логики.
                        # Рассмотрим этот кусок начиная с самой большой вложенности.
                        # Берём предшественников операции n
                        # proc.graph.predecessors(n)

                        # Составляем словарь, в котором ключ - это id предшественника,
                        # а значение - это поле rev ветви из этого предшественника в рассматриваемую операцию n
                        # { p: proc.graph.edges[p, n]['rev'] for p in proc.graph.predecessors(n) }

                        # Составляем массив сетов, в котором всё наоборот: на нулевом месте значения rev, а на первом id операций.
                        # (val, key) for (key, val) in {p: proc.graph.edges[p, n]['rev'] for p in proc.graph.predecessors(n)}.items())

                        # Сортируем по значению rev так, чтобы одинаковые номера групп шли последовательно
                        # sorted((val, key) for (key, val) in {p: proc.graph.edges[p, n]['rev'] for p in proc.graph.predecessors(n)}.items()), lambda x: x[0])

                        # Пакуем id предшественников в группы и помещаем в словарь.
                        # Теперь у нас ключ - это номер группы, а значение - массив id предшественников в этой группе.
                        # То есть, в этом словаре мы собираем в группы операции И и операции ИЛИ.
                        # groupby(sorted((val, key) for (key, val) in {p: proc.graph.edges[p, n]['rev']
                        #   for p in proc.graph.predecessors(n)}.items()), lambda x: x[0]))

                        # На этом этапе выход такой:

                        # 1: A, B, C
                        # 2: D,E

                        # То есть, операции A,B,C объединены логикой ИЛИ. Операции D и E объединены тоже логикой ИЛИ между собой.
                        # Но эти две группы ветвей объединены логикой И.
                        # Физически это обозначает, что для начала выполнения операции нам нужно чтобы одновременно выполнилась
                        # какая-то операция из ABC и какая-то операция из DE.

                        # Теперь соберём логику в новый словарь. Значениями будут нули для тех операций, которые уже выполнились,
                        # единицы - для ещё не завершённых.
                        # [(0 if proc.get_op(gr[1]).Status == OP_FLOW_COMPLETED or proc.get_op(gr[1]).Status == OP_COMPLETED else 1) for gr in g]

                        # Наш большой словарь станет таким:

                        # 1: 0, 0, 1
                        # 2: 0, 0

                        # При условии, что операция С не выполнилась, а остальные выполнились.

                        # Дальше самые важные в этом участке кода строки:
                        # # учёт ограничения на последовательность выполнения операций
                        #                         if sum([reduce(lambda x, y: x * y, v) for v in logic.values()]) == 0:

                        # Функцией reduce мы просто перемножаем 0 и 1 в каждой группе.
                        # Перемножением мы проверяем, что хоть какая-то операция выполнилась. Это логика ИЛИ.
                        # А потом все группы суммируем и этим проверяем, что все операции или группы, объединённые И - выполнились.
                        # То есть, если все предшественники выполнились - можем запускать в работу рассматриваемую операцию.

                        logic = dict((key, [(0 if proc.get_op(gr[1]).Status == OP_FLOW_COMPLETED or
                                                  proc.get_op(gr[1]).Status == OP_COMPLETED else 1) for gr
                                            in g]) for (key, g) in groupby(sorted((val, key) for (key, val) in
                                                                                  {p: proc.graph.edges[p, n]['rev'] for
                                                                                   p
                                                                                   in proc.graph.predecessors(
                                                                                      n)}.items()), lambda x: x[0]))
                        # учёт ограничения на последовательность выполнения операций
                        if sum([reduce(lambda x, y: x * y, v) for v in logic.values()]) == 0:
                            # Исключаем из фронта работы, альтернативные ветви которых уже начали выполняться
                            alt_path_sum = 0
                            for op_id in proc.graph.predecessors(n):
                                alt_path_sum += sum([proc.get_op(p).XP for p in proc.graph.successors(op_id) if
                                                     ((p != n) and
                                                      (proc.graph.edges[op_id, p]['fwd'] == proc.graph.edges[op_id, n][
                                                          'fwd']))])
                            if alt_path_sum == 0:
                                # проверка потенциала доступности процесса и операции
                                if self.get_availability(candidate_operation.ID, time):
                                    OpFront.append(candidate_operation.ID)

            if DEBUG_L2 or DEBUG_FRONT:
                print("\tФронт работ:\n", [self.get_proc_op(o)[1].Name for o in OpFront])

            if self.p: self.p.send("INF: Фронт работ построен")

        def MakeResFront(time):
            "Создание фронта ресурсов в момент времени t. Подготовка ресурсов к загрузке."
            if DEBUG_L2:
                print("Построение фронта ресурсов")

            if self.p: self.p.send("INF: Построение фронта ресурсов на " + str(time))
            del ResFront[:]
            for clust in self.ClustList.values():
                for res in clust.ResList.values():
                    if self.get_res_availability(res.ID, time):
                        res.Release()  # сброс текущей нагрузки на ресурс
                        ResFront.append(res.ID)

            if DEBUG_L2:
                print("\t", [self.get_clust_res(r)[1].Name for r in ResFront])

            if self.p: self.p.send("INF: Фронт ресурсов построен")

        def SolverFIFO(time):
            """Решатель по принципу назначения приоритетов FIFO"""

            # Упорядочивание ресурсов по порядковому номеру
            # OpFront.sort(key=lambda op_id: self.OpPriorMatrix.get(op_id, 0), reverse=True)
            OpFront.sort(key=lambda op_id: self.get_proc_op(op_id)[1].Name, reverse=True)
            for op_id in OpFront:

                result = RES_REJECTED

                # если операция не допускает прерывания
                if not relaxed:
                    # пробуем запустить операцию на том же ресурсе
                    # вспоминаем ресурс с прошлого шага
                    res_id = self.timetable[len(self.timetable) - 1].get((time - 1, op_id), (-1, -1))[0]
                    if len(self.timetable) > 0 and res_id != -1:
                        res = self.get_clust_res(res_id)[1]
                        op_fifo = self.get_proc_op(op_id)[1]
                        # Исключаем не заданную максимальную производительность из расчетов (added by Palich)
                        # intens = min(res.MaxIntense, self.get_productivity(op_id, res.ID))
                        if res.MaxIntense:
                            intens = min(res.MaxIntense, self.get_productivity(op_id, res.ID))
                        else:
                            intens = self.get_productivity(op_id, res.ID)

                        # пробуем, запустится ли на нём операция
                        # result = res.test_load(self.get_proc_op(op_id)[1], intens)

                        result = res.load_operation(op_fifo, intens)  # постановка работы на ресурс
                        if result != RES_REJECTED:
                            if DEBUG_INTERRUPT:
                                print("\t", op_id, "запуск на предыдущем ресурсе", res_id)
                            log_timetable(time, op_id, res_id, intens)  # внесение записи в расписание
                            if DEBUG:
                                print(
                                    "t=" + str(time), op_fifo.Name, "[" + op_id + "] @", res.Name,
                                    "intens=" + str(intens), op_fifo.X,
                                    '->', op_fifo.A, "/", op_fifo.XP, '->', op_fifo.AP)
                            continue  # переход к следующей операции во фронте
                        else:
                            if DEBUG_INTERRUPT:
                                print(op_id, "не запустилась на", res_id)

                # продолжаем просмотр всех ресурсов
                for res_id in reversed(ResFront):
                    # if not relaxed:
                    # if False:
                    #     interr_op = resource_owner(time - 1, res_id)
                    #     if len(interr_op) > 0 and sum([1 for i in interr_op if self.get_proc_op(i[1])[1].AP -
                    #             self.get_proc_op(i[1])[1].XP > 0]):
                    #         continue

                    res = self.get_clust_res(res_id)[1]  # получаем пару (cluster, resource) и выбираем resource

                    # Исключаем не заданную максимальную производительность из расчетов (added by Palich)
                    if res.MaxIntense:
                        intens = min(res.MaxIntense, self.get_productivity(op_id, res_id))
                    else:
                        intens = self.get_productivity(op_id, res_id)
                    if intens != 0:  # если максимальная интенсивность выполнения = 0, то работу запукать не нужно
                        proc_op = self.get_proc_op(op_id)
                        proc_fifo = proc_op[0]
                        op_fifo = proc_op[1]

                        result = RES_PROCESSING

                        # учёт ограничения на параллельность выполнения операций (исключающее или)
                        for p in proc_fifo.graph.predecessors(op_id):  # найти всех предшественников операции
                            for s in proc_fifo.graph.successors(
                                    p):  # для каждого предшественника пройти по всем последователям
                                if s == op_id:
                                    # пропускаем саму себя в списке последователей предшественника
                                    continue
                                # если группа 'fwd' соседней дуги совпадает с 'fwd' текущей дуги
                                if proc_fifo.graph.edges[p, s]['fwd'] == proc_fifo.graph.edges[p, op_id]['fwd']:
                                    if proc_fifo.get_op(s).X != 0:  # если альтернативная ветвь начала работу
                                        result = RES_REJECTED  # запретить выполняться текущей работе
                                        break

                                        #	op_stop_list.append(op_id)
                                        # else:
                                        #	op_stop_list.append(s)					# запретить выполняться другим работам

                        if result != RES_REJECTED:  # если не было запрета на выполнение от параллельных ветвей
                            result = res.load_operation(op_fifo, intens)  # постановка работы на ресурс
                            if result != RES_REJECTED:
                                log_timetable(time, op_id, res_id, intens)  # внесение записи в расписание
                                if DEBUG:
                                    # print(time, op_id, res_id, intens, op.X, op.XP, '->', op.AP)
                                    print(
                                        "t=" + str(time), op_fifo.Name, "[" + op_id + "] @", res.Name, "intens=" +
                                        str(intens), op_fifo.X, '->', op_fifo.A, "/", op_fifo.XP, '->', op_fifo.AP)
                                    print(res.Name, "время наработки", res.Fatigue)
                        else:
                            result = RES_REJECTED

                    else:
                        result = RES_REJECTED  # отклонение работы из-за нулевой интенсивности (ресурс не может выполнять эту операцию)
                    if result != RES_REJECTED:  # если работу не отклонили

                        # DEBUG
                        # print str(time) + ": (" + str(op.ID) + ") " + op.Name + "  ->  ("+ str(res.ID) + ") " + res.Name + ", p: " + str(intens)
                        # END DEBUG
                        break  # переход к следующей работе

            # ликвидация прерываний
            for proc_fifo, op_fifo in self.op_iter():
                conflict_flag = False
                # если работа начата, не завершена, была в расписании на предыдущем шаге, а теперь её нет
                if op_fifo.X != 0 and ((time, op_fifo.ID) in self.timetable[-1] or op_fifo.XP != op_fifo.AP):
                    if ((time - 1, op_fifo.ID) in self.timetable[-1]) and \
                            ((time, op_fifo.ID) not in self.timetable[-1]):
                        if DEBUG_INTERRUPT:
                            print("Разрыв операции", op_fifo.Name, "по зонам видимости")
                        conflict_flag = True
                    if ((time - 1, op_fifo.ID) in self.timetable[-1]) and \
                            ((time, op_fifo.ID) in self.timetable[-1]) and \
                            (self.timetable[-1][(time - 1, op_fifo.ID)][0] !=
                             self.timetable[-1][(time, op_fifo.ID)][0]):
                        if DEBUG_INTERRUPT:
                            print("Разрыв операции", op_fifo.Name, "по ресурсу")
                        conflict_flag = True
                    self.conflict_count += 1
                if not options.get('relaxed') and conflict_flag:
                    op_start_time = operation_start(op_fifo.ID)
                    if op_start_time is not None:
                        # откат на точку, предшествующую прерыванию и запрет выполнения одной из операций
                        if DEBUG_INTERRUPT:
                            print("Запрет на выполнение", self.get_proc_op(op_fifo.ID)[1].Name, "c", op_start_time,
                                  "до", time)
                        self.set_restriction(op_fifo.ID, op_start_time, time)
                        if DEBUG_INTERRUPT:
                            print("Откат на начало прерванной операции -> ", op_start_time)
                        self.execute_plan(0, op_start_time - 1)
                        if DEBUG_INTERRUPT:
                            print("Текущее время:", self.time)
                        return
            if DEBUG_L2:
                print("Действующие ограничения", self.restriction)

        def SolverLIFO(time):
            "Решатель по принципу LIFO"
            OpFront.reverse()
            for job in OpFront:
                for res in ResFront:
                    intens = self.Productivity(job, res, time)
                    if intens != 0:  # считаем, что если максимальная интенсивность выполнения = 0, то работу запукать не нужно.
                        Result = res.load_operation(job, intens)  # постановка работы на ресурс
                    # print job.Name + ", " + res.Name + " p: " + str(intens)
                    else:
                        Result = RES_REJECTED
                    if Result != RES_REJECTED:  # если работу не отклонил
                        log_timetable(time, job, res)  # внесение записи в расписание
                        break  # переход к следующей работе

        def SolverNone(time):
            "Пустой решатель"
            pass

        def SolverExec(time):
            """Имитация исполнения плана по существующему расписанию"""
            for job_id in OpFront:
                # если работа выполнялась в текущий помент времени...
                if self.timetable[-1].get((time, job_id)):
                    for res_id in ResFront:
                        # ещё и на рассматриваемом ресурсе...
                        if self.timetable[-1].get((time, job_id))[0] == res_id:
                            # ...то управление включено и потоковое управление берётся из расписания
                            u = 1
                            up = self.timetable[-1].get((time, job_id))[1]
                            res = self.get_clust_res(res_id)[1]
                            op = self.get_proc_op(job_id)[1]

                            load_result = res.load_operation(op, up)  # постановка работы на ресурс
                            if load_result != RES_REJECTED:  # если работу не отклонил
                                if DEBUG_EXEC:
                                    print("\tВыполнение", op.Name, "uⁿ", up, op.X, '->', op.A, op.XP, '->', op.AP)

        def SolverPULP(time):
            """Решатель, оптимизирующий с помощью модуля PuLP https://projects.coin-or.org/PuLP"""

            # Create the 'prob' variable to contain the problem data
            prob = LpProblem(r"Задача максимизации Гамильтониана".replace(' ', '_'), LpMaximize)
            # количество управляющих воздействий: 0/1 - для каждой связки операции и ресурса
            m = len(OpFront) * len(ResFront)

            if m == 0:
                if DEBUG_PULP:
                    print("⭕️ Пустой фронт работ")
            else:
                # целевая функция

                # H1
                # в списке хранятся коэффициенты перед управляющими воздействиями в гамильтониане
                # PAVLOV: 3.1.1 (коэффициенты при управлении операциями в H1 Гамильтониана)
                c = []
                jr = []
                for job_id in OpFront:
                    for res_id in ResFront:
                        # c.append(self.OpPriorMatrix[job_id] + self.ResPriorMatrix[res_id])
                        # в гамильтониане перед каждым основным управлением
                        # стоит значение переменной сопряжённой системы уравнений
                        c.append(self.OpPriorMatrix[job_id] +
                                 self.ResPriorMatrix[res_id] +
                                 5000 - self.get_clust_res(res_id)[1].price)  # max price - price
                        # self.penalty.get(job_id, (0,0,0))[2])
                        if DEBUG_L1:
                            jr.append((self.get_proc_op(job_id)[1].Name, res_id, c[-1]))
                            print("Вклады в Гамильтониан", self.OpPriorMatrix[job_id],
                                  self.ResPriorMatrix[res_id],
                                  5000 - self.get_clust_res(res_id)[1].price)
                # /PAVLOV: 3.1.1 (коэффициенты при управлении операциями в H1 Гамильтониана)

                # список искомых основных управляющих воздействий
                x = []

                # H2
                # список значений коэффициентов перед потоковым управлением
                cp = []
                # список искомых потоковых управлений от 0 до максимальной интенсивности обработки потока
                # определённой операции на определённом ресурсе
                xp = []

                # далее управления вычисляются из ограничений, оптимизация не происходит, так как нет конфликта
                # H3
                cphi1 = []
                # H4
                cphi2 = []
                # H5
                cphi3 = []
                # H6
                cpv1 = []
                # H7
                cpv2 = []

                # PuLP сортирует выходные переменные по имени. Необходимо имена задать в виде индексов,
                # а затем отсортировать переменные, преобразуя строки в целые числа
                # PAVLOV: 3.1.2 (коэффициенты при управлении потоками в H2 Гамильтониана)
                index_cntr = 0
                for job_id in OpFront:
                    for res_id in ResFront:
                        product = self.get_productivity(job_id, res_id)  # максимальная интенсивность выполнения

                        # H1
                        # основные управляющие воздействия, которые необходимо найти - целочисленные от 0 до 1.
                        # А также Запрет запуска основного управления при максимальной интенсивности = 0
                        x.append(LpVariable('u_%d_o%s_r%s' % (index_cntr, job_id, res_id), 0, 0 if product == 0 else 1,
                                            LpInteger))
                        index_cntr += 1

                        # потоковые управляющие воздействия, которые необходимо найти -
                        # вещественное число от 0 до Заданной продуктивности
                        xp.append(LpVariable('u_%d_p%s_r%s' % (index_cntr, job_id, res_id), 0, product, LpContinuous))
                        index_cntr += 1

                        # TODO добавить значения 𝜂 и 𝓆

                        # H2
                        # в гамильтониане перед каждым потоковым управлением стоит коэффициент сопряжённой системы уравнений
                        cp.append(self.StreamPriorMatrix[job_id])

                        # H3
                        cphi1 = []
                        # H4
                        cphi2 = []
                        # H5
                        cphi3 = []
                        # H6
                        cpv1 = []
                        # H7
                        cpv2 = []
                # /PAVLOV: 3.1.2 (коэффициенты при управлении потоками в H2 Гамильтониана)

                if DEBUG_L1:
                    print(cp)

                # формирование целевой функции вида c*x + cp*xp - Гамильтониан
                prob += lpDot(x, c) + lpDot(xp, cp), r"Гамильтониан"

                # Ограничения
                b = []
                # создание вектора b, в котором выставлены единицы у управлений операций и ресурсов из фронта

                # PAVLOV: 2.1.7 (1)
                for (j, op_id) in enumerate(OpFront):
                    # x + x + x + x + x + x + x + x + x + x + x + x
                    # |_______| - фронт ресурсов
                    # 1 + 1 + 1 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 <= 1 - операция №1
                    # 0 + 0 + 0 + 1 + 1 + 1 + 0 + 0 + 0 + 0 + 0 + 0 <= 1 - операция №2 и т.д.
                    del b[:]
                    for i in range(0, j * len(ResFront)): b.append(0)
                    for i in range(j * len(ResFront), (j + 1) * len(ResFront)): b.append(1)
                    for i in range((j + 1) * len(ResFront), len(OpFront) * len(ResFront)): b.append(0)
                    op = self.get_proc_op(op_id)[1]
                    # сумма управлений для каждой операции по всем ресурсам не более 1
                    prob += lpDot(x, b) <= 1, r"Ограничение на параллельное выполнение операции " + op.Name + "_" + str(
                        op.ID)
                    # /PAVLOV: 2.1.7 (1)

                # PAVLOV: 2.1.7. (2)
                for (j, res_id) in enumerate(ResFront):
                    del b[:]
                    for k in range(len(OpFront)):
                        for ri in range(0, j):
                            b.append(0)
                        b.append(1)
                        for ri in range(j + 2, len(ResFront) + 1):
                            b.append(0)

                    res = self.get_clust_res(res_id)[1]
                    # сумма управлений по всем операциям для каждого ресурса не более максимальной производительности
                    prob += lpDot(x,
                                  b) <= res.MaxThreads, r"Ограничение вместительности ресурса " + res.Name + "_" + str(
                        res.ID)

                    # сумма интенсивностей по всем операциям для каждого ресурса не более максимальной пропускной способности
                    prob += lpDot(xp,
                                  b) <= res.MaxIntense, r"Ограничение производительности ресурса " + res.Name + "_" + str(
                        res.ID)
                # /PAVLOV: 2.1.7. (2)

                # PAVLOV: здесь ПСА реализовал аналог формул (2.1.8 – 2.1.11)
                for constrx, constrxp in zip(x, xp):
                    prob += constrxp - constrxp.upBound * constrx <= 0, r"Запрет запуска потока " + constrxp.name + \
                            r" без основного управления " + constrx.name

                for (j, op_id) in enumerate(OpFront):
                    proc = self.get_proc_op(op_id)[0]
                    del b[:]
                    # заполним нулями вектор коэффициентов при управлении
                    for i in range(0, len(OpFront) * len(ResFront)):
                        b.append(0)

                    for p in proc.graph.predecessors(op_id):  # найти всех предшественников операции

                        if len(list(proc.graph.successors(
                                p))) <= 1: continue  # если нет альтернативных ветвей, пропустить разбор

                        for s in proc.graph.successors(p):  # для каждого предшественника пройти по всем последователям

                            # Проверка альтернативных ветвей

                            if proc.graph.edges[p, s]['fwd'] == proc.graph.edges[p, op_id]["fwd"]:
                                # если группа 'fwd' соседней дуги совпадает с 'fwd' текущей дуги
                                if s != op_id and proc.get_op(s).X != 0:  # если альтернативная ветвь начала работу
                                    for k, res in enumerate(ResFront):
                                        prob += x[j * len(ResFront) + k] <= 0, r"Запрет запуска операции " + \
                                                x[j * len(ResFront) + k].name + r", если работала альтернативная ветвь"

                                if s not in OpFront:
                                    continue

                                alt_id = OpFront.index(s)
                                for i in range(alt_id * len(ResFront), (alt_id + 1) * len(ResFront)):
                                    b[
                                        i] = 1  # выставим единицы альтернативным операциям (для каждого ресурса во фронте)

                    if 1 in b:
                        prob += lpDot(x, b) <= 1, r"Ограничение на выполнение операций исключающих ИЛИ " + str(op_id)

                # /PAVLOV: здесь ПСА реализовал аналог формул (2.1.8 – 2.1.11)

                if WRITE_FILE:
                    # запись проблемы
                    prob.writeLP("test3.lp" + str(self.iteration))
                    # print prob.variables()

                # Solve the problem using the default solver
                solver = pulp.PULP_CBC_CMD(keepFiles=True, msg=False)
                # solver.tmpDir = 'TMP'
                prob.solve(solver)

                if DEBUG:
                    if LpStatus[prob.status] != 'Optimal':
                        print("Не оптимальное решение", LpStatus[prob.status])
                    else:
                        print("Найдено оптимальное решение", LpStatus[prob.status])

                if WRITE_FILE:
                    # Print the value of the objective

                    f = open('test2.lp' + str(self.iteration), "w")
                    for v in prob.variables():
                        # if v.varValue != 0:
                        f.write(str(v.name) + " -> " + str(v.varValue) + "\r\n")
                        # print v.name, "=", v.varValue
                    f.close()

                # v = iter(prob.variables())  # изъятие вектора управлений из решателя в список control

                # PuLP is silly and sorts the variables by name before returning them,
                # so we need to re-sort them in numerical order.

                solution = [s.varValue for s in sorted(prob.variables(), key=lambda v: int(v.name.split('_')[1]))]
                # from pprint import pprint
                # print(solution)

                # PAVLOV CODE
                # self.Priorities_all = {}
                i = 0
                for job_id in OpFront:
                    for res_id in ResFront:
                        if solution[i]: self.Priorities_all[job_id] = c[i]
                        i += 1
                # print(self.Priorities_all)

                # PAVLOV /CODE

                # выполнение операций со включенным управлением
                # uList = iter(control)
                # upList = iter(streamcontrol)
                ucntr = 0  # счётчик включенных управлений
                uList = iter(solution)
                for job_id in OpFront:
                    for res_id in ResFront:
                        try:
                            u = next(uList)
                            up = next(uList)
                            if u == float("1.0"):  # если переменная из SOLVER равна единице
                                ucntr += 1
                                res = self.get_clust_res(res_id)[1]
                                op = self.get_proc_op(job_id)[1]

                                # определение точки разрыва операции
                                interrupted_operations = resource_owner(time - 1, res.ID)
                                interruption_flag = False

                                old_res = self.get_clust_res(self.timetable[-1].get((time - 1, op.ID), (-1, -1))[0])

                                # если операция может быть запущена на ресурсе И ранее она выполнялась
                                # И на другом ресурсе - операция скачет по ресурсам
                                if res.test_load(op, up) != RES_REJECTED and op.X != 0 and old_res and \
                                        self.timetable[-1].get((time - 1, op.ID), (-1, -1))[0] != res_id:
                                    old_res = old_res[1]
                                    h1 = self.OpPriorMatrix[job_id] + \
                                         self.ResPriorMatrix[res_id] + \
                                         self.penalty.get(job_id, (0, 0, 0))[2]

                                    h2 = self.OpPriorMatrix[job_id] + \
                                         self.ResPriorMatrix[old_res.ID] + \
                                         self.penalty.get(job_id, (0, 0, 0))[2]

                                    if DEBUG_INTERRUPT:
                                        print('❎ Намечается разрыв', op.Name, 'по ресурсу')
                                        if h1 == h2:
                                            print('Можно бы ликвидировать')
                                            if old_res.test_load(op, up) == RES_REJECTED:
                                                print('Но на используемом ресурсе уже нельзя запускать')

                                    # continue
                                # СЛУЧАЙНО ОПРЕДЕЛЯЮ ПРОДОЛЖЕНИЕ (ЗАПРЕТ ПРЕРЫВАНИЯ) (??)
                                if DEBUG_L1 and up == 0:
                                    print("⚠️ Запуск с нулевой интенсивностью", op.Name, op.ID, res.Name, res.ID)

                                load_result = res.load_operation(op, up)  # постановка работы на ресурс
                                if load_result != RES_REJECTED:  # если работу не отклонил
                                    log_timetable(time, job_id, res_id, up)  # внесение записи в расписание

                                    if self.logger and load_result:
                                        self.logger.put({
                                            "message": 'Операция {} - {}'.format(job_id, load_result),
                                            "variables": {
                                                "operation": {
                                                    "id": job_id,
                                                    "template_id": op.template_id,
                                                    "process": self.get_proc_op(job_id)[0].ID,
                                                    "status": load_result,
                                                    "name": op.Name
                                                }
                                            }
                                        })

                                    if DEBUG_EXEC:
                                        print("Выполнение", op.Name, "uⁿ", up, op.X, '->', op.A,
                                              op.XP, '->', op.AP, '@', res.Name)
                                else:
                                    if DEBUG_EXEC:
                                        print("Ресурс", res.Name, "отказался выполнять работу", op.Name)
                        except StopIteration:
                            break

                if not ucntr:
                    if DEBUG_EXEC:
                        print("Управлене не включалось")

                if DEBUG_EXEC:
                    print("Гамильтониан:", value(prob.objective))

                if self.logger and not (time % HAMILTONIAN_THINNING):
                    self.logger.put({
                        "message": 'H = {} - Гамильтониан'.format(value(prob.objective), ),
                        "variables": {
                            "hamiltonian": [self.time, value(prob.objective)]
                        }

                    })

            # Разрывы оцениваются даже при пустов фронте работ

            # оценим разрывы
            for proc, op in self.op_iter():
                # op = self.get_proc_op(job_id)[1]

                # если работа начата, не завершена, была в расписании на предыдущем шаге, а теперь её нет
                # if op.X != 0 and \
                #         ((op.XP != op.AP and
                #         (time - 1, op.ID) in self.timetable[-1] and
                #         (time, op.ID) not in self.timetable[-1]) or
                #         ((time, op.ID) in self.timetable[-1] and
                #             (time - 1, op.ID) in self.timetable[-1] and (time, op.ID) in self.timetable[-1] and
                #             self.timetable[-1].get((time - 1, op.ID), (-1, -1))[0] !=
                #             self.timetable[-1].get((time, op.ID), (-1, -1))[0])
                #         ):
                interruption_type = 0

                # Pavlov TODO: проверить правильность определения завершения операции при снятии
                # ограничения на директивные сроки выполнения операции
                # (через status?)
                # если операция началась и не закончилась
                if op.Status == OP_EXEC:
                    # if op.X != 0 and op.XP != op.AP:
                    # если операция была в расписании и пропала
                    if (time - 1, op.ID) in self.timetable[-1] and (time, op.ID) not in self.timetable[-1]:
                        interruption_type = 1  # прерывание первого типа, зоны видимости
                        if DEBUG_INTERRUPT:
                            print("❌ Операция", op.Name, "пропала из расписания")
                if op.X != 0 and (time, op.ID) in self.timetable[-1]:
                    if ((time, op.ID) in self.timetable[-1]) and ((time - 1, op.ID) in self.timetable[-1]):
                        int_old_res_id = self.timetable[-1].get((time - 1, op.ID))[0]
                        int_new_res_id = self.timetable[-1].get((time, op.ID))[0]
                        if int_old_res_id != int_new_res_id:
                            interruption_type = 2  # прерывание второго типа, переброс ресурса
                            if DEBUG_INTERRUPT:
                                print("🌀️ Операция", op.Name, "сменила ресурс",
                                      self.timetable[-1].get((time - 1, op.ID))[0], "->",
                                      self.timetable[-1].get((time, op.ID))[0])
                if interruption_type != 0:
                    self.conflict_count += 1
                    if not options.get('relaxed'):
                        # определим, кто обслуживал операцию
                        res = self.timetable[-1][(time - 1, op.ID)][0]
                        # ресурс мог выполнять несколько операций, выберем ту, которая началась раньше
                        interrupted = min(resource_owner(time - 1, res), key=lambda t: t[0])
                        # выясним, кто прервал операцию
                        if (len(resource_owner(time, res)) > 0):
                            interruptor = min(resource_owner(time, res), key=lambda t: t[0])
                            if not SIMPLE_DECISION:
                                if DEBUG_INTERRUPT:
                                    print("\t", self.get_proc_op(interruptor[1])[1].Name, "вытесняют", op.Name)
                                    print("\tвладелец ресурса", self.get_clust_res(res)[1].ID, "на предыдущем шаге -",
                                          [self.get_proc_op(rsn[1])[1].Name for rsn in resource_owner(time - 1, res)])

                                    print("")
                                    print("v" * 30, "Рассмотрение варианта 1", "v" * 30)
                                dyn_clone_1 = clone_model(self)
                                # dyn_clone_1.execute_plan(0, interrupted[0] - 1)
                                if DEBUG_INTERRUPT:
                                    print("Запрет на выполнение", self.get_proc_op(interrupted[1])[1].Name, "c",
                                          interrupted[0], "до", time + 1)
                                dyn_clone_1.reset_executed(clear_restrictions=False)
                                dyn_clone_1.set_restriction(interrupted[1], interrupted[0], time + 1)
                                if DEBUG_INTERRUPT:
                                    print("Действующие ограничения", dyn_clone_1.restriction)
                                dyn_clone_1.calculate_plan(dict(method="PULP", relaxed=True, debug_tab=debug_tab + 1))
                                # dyn_clone_1.calculate_plan(dict(method="FIFO", relaxed=True))
                                conflicts1 = dyn_clone_1.QltList['J0'][-1]
                                del dyn_clone_1
                                if DEBUG_INTERRUPT:
                                    print("^" * 30, "  Окончание варианта 1 ", "^" * 30)

                                    print("")
                                    print("v" * 30, "Рассмотрение варианта 2", "v" * 30)
                                dyn_clone_1 = clone_model(self)
                                # dyn_clone_1.execute_plan(0, interrupted[0] - 1)
                                dyn_clone_1.reset_executed(clear_restrictions=False)
                                if DEBUG_INTERRUPT:
                                    print("Запрет на выполнение", self.get_proc_op(interruptor[1])[1].Name, "c", time,
                                          "до", time + 1)
                                dyn_clone_1.set_restriction(interruptor[1], time, time + 1)
                                if DEBUG_INTERRUPT:
                                    print("Действующие ограничения", dyn_clone_1.restriction)
                                # dyn_clone_1.calculate_plan(dict(method="FIFO", relaxed=True))
                                dyn_clone_1.calculate_plan(dict(method="PULP", relaxed=True, debug_tab=debug_tab + 1))
                                conflicts2 = dyn_clone_1.QltList['J0'][-1]
                                del dyn_clone_1
                                if DEBUG_INTERRUPT:
                                    print("^" * 30, "  Окончание варианта 2 ", "^" * 30)

                                # conf_res = 1 if conflicts1 < conflicts2 \
                                #    else (2 if conflicts1 > conflicts2 else randrange(1, 2))

                                if conflicts1 < conflicts2:
                                    if DEBUG_INTERRUPT:
                                        print(conflicts1, "<", conflicts2)
                                        print("Первый вариант менее конфликтный: запрет на выполнение",
                                              self.get_proc_op(interrupted[1])[1].Name, "c",
                                              interrupted[0], "до", time + 1)
                                    self.set_restriction(interrupted[1], interrupted[0], time)
                                else:
                                    if DEBUG_INTERRUPT:
                                        print(conflicts1, ">", conflicts2)
                                        print("Второй вариант менее конфликтный: запрет на выполнение",
                                              self.get_proc_op(interruptor[1])[1].Name, "c", time,
                                              "до", time + 1)
                                    self.set_restriction(interruptor[1], time, time + 1)
                            else:
                                # при решении простым способом запрет на прерывание устанавливается случайно
                                self.set_restriction(interruptor[1], time, time + 1) if randrange(0, 10) > 5 \
                                    else self.set_restriction(interrupted[1], interrupted[0], time)
                        else:
                            # операцию никто не прерывал
                            if interruption_type == 1:
                                pass
                            elif interruption_type == 2:
                                old_res_id = self.timetable[-1].get((time - 1, op.ID))[0]
                                new_res_id = self.timetable[-1].get((time, op.ID))[0]
                                h1 = self.OpPriorMatrix[op.ID] + \
                                     self.ResPriorMatrix[old_res_id] + \
                                     self.penalty.get(op.ID, (0, 0, 0))[2]

                                h2 = self.OpPriorMatrix[op.ID] + \
                                     self.ResPriorMatrix[new_res_id] + \
                                     self.penalty.get(op.ID, (0, 0, 0))[2]

                                if h1 == h2:
                                    if DEBUG_INTERRUPT:
                                        print('Можно бы ликвидировать')
                                    if self.get_clust_res(old_res_id)[1].test_load(op) == RES_REJECTED:
                                        if DEBUG_INTERRUPT:
                                            print('Но на используемом ресурсе уже нельзя запускать')
                                elif h1 < h2:
                                    if DEBUG_INTERRUPT:
                                        print('Необходимо дождаться более приоритетного ресурса')

                            if DEBUG_INTERRUPT:
                                print("Разрыв из-за зоны видимости или освобождения более приоритетного ресурса")
                                print("Запрет на выполнение", self.get_proc_op(interrupted[1])[1].Name,
                                      "c", interrupted[0], "до", time + 1)
                            self.set_restriction(interrupted[1], interrupted[0], time)

                        # выполнить план надо до момента начала прерванной операции, поэтому time - 1
                        if DEBUG_INTERRUPT:
                            print("Откат на начало прерванной операции -> ", interrupted[0])

                        self.reset_executed(clear_timetable=False,
                                            clear_restrictions=False)  # сбросить текущее состояние модели
                        self.OpPriorMatrix = self.operation_init_conditions.copy()
                        self.StreamPriorMatrix = self.stream_init_conditions.copy()
                        self.ResPriorMatrix = self.resource_init_conditions.copy()
                        # self.normalize_left()
                        self.integrate(0, interrupted[0] - 1, {'method': 'EXEC'})
                        self.time = interrupted[0] - 1

                        if DEBUG_INTERRUPT:
                            print("Текущее время:", self.time)
                            print("Действующие ограничения", self.restriction)
                        return

        def log_timetable(time, job_id, res_id, intens):
            """Запись в таблицу расписаний.
            :param time: текущее время
            :param job_id: выполняемая операция
            :param res_id: выполняющий ресурс
            :param intens: интенсивность обработки
            """
            self.timetable[-1][(time, job_id)] = (res_id, intens)

        def resource_owner(check_time, resource_id):
            """Поиск операции, которая занимает ресурс
            :param check_time: момент времени занятости ресурса
            :param resource_id: идентификатор занятого ресурса
            :return: кортеж (время начала, id операции)
            """
            execution_row = list()
            if len(self.timetable[-1]) != 0:
                # a = {j:k for j,k in self.timetable[-1] if j[0] == check_time}.keys()[[i[0] for i in self.timetable[-1].values()].index(resource_id)]
                execution_point = [(j, k) for (j, k), (l, m) in self.timetable[-1].items()
                                   if (l == resource_id) and (j == check_time)]

                for ep in execution_point:
                    execution_dict = {j: k for (j, k), (l, m) in self.timetable[-1].items()
                                      if (l == resource_id) and (k == ep[1])}
                    start_time = min(execution_dict)  # , key=execution_row.get)

                    execution_row.append((start_time, execution_dict[start_time]))

            return execution_row

        def operation_start(operation_id):
            """Поиск времени начала операции
            :param operation_id: идентификатор операции
            :return: время начала операции
            """
            start_time = None
            if len(self.timetable[-1]) != 0:
                # a = {j:k for j,k in self.timetable[-1] if j[0] == check_time}.keys()[[i[0] for i in self.timetable[-1].values()].index(resource_id)]

                # получение листа времени работы для интересующей операции
                execution_dict = [j for (j, k) in self.timetable[-1] if k == operation_id]
                start_time = min(execution_dict)  # , key=execution_row.get)

            return start_time

        if DEBUG:
            print("Старт")
        t1 = time()

        ##################################
        #								 #
        #  Основной цикл интегрирования	 #
        #								 #
        ##################################

        if self.p: self.p.send("INF: Планирование от " + str(ts) + " до " + str(tf) + " (" + method + ")")
        if tf <= ts:
            return

        # назначение начального времени
        self.time = ts
        # Внимание! self.time может быть изменено внутри решателя при возникновении разрывов

        # подготовка консольного вывода
        if DEBUG_CTRL:
            # операции
            self.ograph = {n[1].ID: list() for n in self.op_iter()}
            # потоки
            self.pgraph = {n[1].ID: list() for n in self.op_iter()}
            # визуальное представление
            self.work = {n[1].ID: list() for n in self.op_iter()}

            print("Планирование от " + str(ts) + " до " + str(tf) + " (" + method + ")")

        # в списке хранятся коэффициенты перед управляющими воздействиями в гамильтониане
        # PAVLOV: 3.1.1 (коэффициенты при управлении операциями в H1 Гамильтониана)
        global index_ham
        global ham_file
        global csv_data
        csv_data = [['time', 'Job', 'Res', 'C', 'solution']]

        empty_loops = 0  # подсчёт количества шагов с пустым фронтом работ
        while self.time <= tf:  # проход по заданному интервалу

            # PAVLOV: плохая заглушка для борьбы с биениями
            # TODO добавить прекращение из-за биений
            # if empty_loops > tf: break

            # input('Задержка...')
            # while self.time <= min(tf, self.D):  # проход по заданному интервалу
            # all_done = False
            # while not all_done:  # проход по заданному интервалу
            if DEBUG_L1:
                print()
                print("Время:", self.time)
            # TODO: вынести в параллельные процессы
            # построение фронта работ
            MakeOpFront(self.time)
            # построение фронта ресурсов
            MakeResFront(self.time)

            # назначаем работы на ресурсы - главный решатель
            if method == "PULP":
                SolverPULP(self.time)
            elif method == "LIFO":
                SolverLIFO(self.time)
            elif method == "NONE":
                SolverNone(self.time)
            elif method == "EXEC":
                SolverExec(self.time)
            else:
                SolverFIFO(self.time)

            self.calculate_priorities()

            # определение завершения процессов
            procs_completed = 0
            for prc in self.ProcList.values():
                # найти последние операции процессов
                for nd in prc.graph.nodes():
                    if len(list(prc.graph.successors(nd))) == 0:
                        if prc.get_op(nd).Status in [STREAM_COMPLETED, FULL_COMPLETED]:
                            procs_completed = procs_completed + 1
                            if DEBUG_L1:
                                print("Завершился процесс", prc.Name)

            if method not in ['EXEC', 'NONE']:
                if len(self.ProcList) <= procs_completed:  # теоретически д.б. "==", расчет procs_completed?
                    # all_done = True
                    tf = self.time
                    print("\t" * debug_tab, "✅ Все процессы завершены, план выполнен за", tf)
                else:
                    if empty_loops > 7000:
                        print("⚠️ Много пустых итераций. Прерываем")
                        tf = self.time
                    else:
                        tf = self.time + 10
                        # tf = self.time*2    # PAVLOV: пытаемся нелинейно расширять горизонт планирования - меньше итераций, когда не хватает времени

            self.time += self.Step
            empty_loops += 1  # считаем циклы, чтобы не зациклиться

        self.D = self.time

        # /PAVLOV: 3.1.1 (коэффициенты при управлении операциями в H1 Гамильтониана)
        i = 0
        for time_time, job_id in self.timetable[-1].keys():
            res_id = self.timetable[-1][(time_time, job_id)][0]
            csv_data.append([time_time, self.get_proc_op(job_id)[1].Name + '(' + str(job_id) + ')',
                             self.get_clust_res(res_id)[1].Name + '(' + str(res_id) + ')',
                             str(self.Priorities_all.get(job_id, 0)).replace('.', ','),
                             str(int(1 if (time_time, job_id) in self.timetable[-1] else 0))])
            # self.penalty.get(job_id, (0,0,0))[2])
            i += 1
        # /PAVLOV: 3.1.1 (коэффициенты при управлении операциями в H1 Гамильтониана)
        index_ham += 1
        ham_file = open(os.path.join(dir_name, 'hamiltonian_' + str(index_ham) + '.csv'), 'w', newline='\n')
        writer = csv.writer(ham_file, dialect='excel', delimiter=';')
        writer.writerows(csv_data)
        ham_file.close()

        if DEBUG_L2:
            print('*' * 10, 'fwd psi o')
            for ogi, ogv in self.ograph.items():
                print(self.get_proc_op(ogi)[1].Name, ogv)
            print()
            print('*' * 10, 'fwd psi p')
            for pgi, pgv in self.pgraph.items():
                print(self.get_proc_op(pgi)[1].Name, pgv)
            print()
        if DEBUG_CTRL:
            print('*' * 10, method, 'fwd u')

            for mt in range(0, int(self.D) + 1):
                sys.stdout.write(str(mt).zfill(2))

            print()

            for op, g in sorted(self.work.items(), key=lambda k: k[0]):
                if bool(set(g) & set(['1', '2', '3'])):
                    for p in g:
                        print(p, end=' ')

                    print(self.get_proc_op(op)[1].Name, "[" + self.get_proc_op(op)[1].ID + "]")

        t2 = time()
        if DEBUG:
            print("Расчёт занял", round(t2 - t1, 3), "сек")
        if self.p:
            self.p.send("INF: Расчёт занял " + str(round(t2 - t1, 3)))

    def Assess(self, e=1):
        """Оценка качества плана. Принятие решения о следующей итерации на основе сравнения обобщённого показателя
        качества с предыдущим значением. Сравнение производится с точностью до e, по умолчанию 0.01.
        Возвращает True если показатели совпали и False, если нет и требуется повторная итерация."""

        # self.QltList[0] - это Обобщённый показатель качества

        if DEBUG_Q:
            print("Расчёт показателей качества")

        # J1 и J2
        residual = 0  # "Невязка" - показатель неполноты выполнения операций
        residual_p = 0  # "Невязка" - показатель неполноты обработки потока

        gantt_list = list()

        def add_scsr(gnt, proc, op_id):
            """
            Рекурсивное суммирование основных и потоковых невязок по выполнявшимся ветвям графа
            :param gnt: список, в который добавляются уже учтённые работы
            :param proc: процесс, по которому строится список
            :param op_id: стартовая работа
            :return: (основная невязка, потоковая невязка)
            """
            proc_residual = 0
            proc_residual_p = 0
            op = proc.get_op(op_id)
            # запись работ в общий список во избежание повторного учёта
            if not (proc, op) in gnt:
                gnt.append((proc, op))
                # if proc.graph.edge[op_id][scsr]['fwd']
                proc_residual += (op.A - op.X) ** 2
                proc_residual_p += (op.AP - op.XP) ** 2
                # if PRINT:
                #     print('\t\tAppend', proc.ID, op.ID, "J =", proc_residual, "Jp =", proc_residual_p)

            # Исключаем из обхода альтернативные ветви
            # Группируем по номерам fwd дуги, идущие к последователям
            logic = dict((key, [{gr[1]: (proc.get_op(gr[1]).A - proc.get_op(gr[1]).X)} for gr
                                in g]) for (key, g) in groupby(sorted((val, key) for (key, val) in
                                                                      {p: proc.graph.edges[op_id, p]['fwd'] for p
                                                                       in proc.graph.successors(
                                                                          op_id)}.items()), lambda x: x[0]))
            # Рассматриваем только тех последователей, которые являются безальтернативными или выполнились.
            # Если последователь одной из параллельных ветвей не выполнился - не рассматриваем его и всю его ветвь.
            # todo предусмотреть случай, когда все не выполнились (обрыв по концу интервала планирования, например)
            alt_scsr = map(lambda x: x[0], filter(lambda x: len(x) > 0, [[list(i2)[0] for i2 in i if (((len(i) == 1) or
                                                                                                       ((list(
                                                                                                           i2.values())[
                                                                                                             0] == 0) and (
                                                                                                                len(
                                                                                                                    i) > 1))))]
                                                                         for i in logic.values()]))
            # alt_scsr = [[list(i2)[0] for i2 in i if (((len(i) == 1) or
            #                                           ((list(i2.values())[0] == 0) and (len(i) > 1))))][0]
            #             for i in logic.values()]
            # для каждого последователя выполняется рекурсивный вызов
            for scsr in alt_scsr:
                # for scsr in proc.graph.successors_iter(op_id):
                scsr_op = proc.get_op(scsr)

                # if ((len(proc.graph.successors(op_id)) > 1) and (scsr_op.A - scsr_op.X == 0)) or \
                #         (len(proc.graph.successors(op_id)) < 2):
                residual_tuple = add_scsr(gnt, proc, scsr)
                proc_residual += residual_tuple[0]
                proc_residual_p += residual_tuple[1]

            return proc_residual, proc_residual_p

        ways_cntr = 0
        for proc in self.ProcList.values():
            # определяем начальные и конечные узлы
            # todo: replace with MultiDiGraph.in_edges_iter([nbunch, data, keys])
            start_nodes = list()
            end_nodes = list()
            for node in proc.graph.nodes():
                if sum(1 for _ in proc.graph.predecessors(node)) == 0:
                    start_nodes.append(node)
                if sum(1 for _ in proc.graph.successors(node)) == 0:
                    end_nodes.append(node)

            # для всех стартовых работ выполняется рекурсивный поиск выполнявшихся последователей
            for start_node in start_nodes:
                residual_tuple = add_scsr(gantt_list, proc, start_node)
                residual += residual_tuple[0]
                residual_p += residual_tuple[1]

            for sn in start_nodes:
                for en in end_nodes:
                    ways_cntr += len(list(nx.all_simple_paths(proc.graph, sn, en)))

        if DEBUG_GRAPH:
            print("Количество узлов", proc.graph.number_of_nodes())
            print("Количество рёбер", proc.graph.number_of_edges())
            print("Количество альтернативных путей", ways_cntr)

        self.QltList["J1"].append(residual / 2)
        if self.p:
            self.p.send("INF: Показатель неполноты выполнения операций: " + str(self.QltList["J1"][-1]))
        if DEBUG_Q:
            if self.QltList["J1"][0] > 0:
                print("J1 = ", self.QltList["J1"][-1], "\tневязка по отведённому времени")

        self.QltList["J2"].append(residual_p / 2)
        if self.p:
            self.p.send("INF: Показатель неполноты обработки потока: " + str(self.QltList["J2"][-1]))
        if DEBUG_Q:
            if self.QltList["J2"][0] > 0:
                print("J2 = ", self.QltList["J2"][-1], "\tневязка по потоку")

        # Показатель стоимости реализации плана
        j3_sum = 0
        for sc_clust, sc_res in self.res_iter():
            j3_sum += sc_res.cost
        self.QltList["J3"].append(j3_sum)
        if DEBUG_Q:
            if self.QltList["J3"][0] > 0:
                print("J3 = ", self.QltList["J3"][-1], "\tстоимость реализации плана ( ✕", self.QltList["J3"][0], ")")
        if False and self.logger:
            if self.QltList["J3"][0] > 0 and len(self.QltList["J3"]) != 3:
                self.logger.put({
                    "message": 'J3 = {} стоимость реализации плана ( ✕ {})'.format(self.QltList["J3"][-1],
                                                                                   self.QltList["J3"][0]),
                    "variables": {
                        "quality_j3": [len(self.QltList["J3"]) - 2, self.QltList["J3"][-1]]
                    }

                })

        # J4 Показатель нарушения директивных сроков
        j4_sum = 0
        for j_proc, j_op in self.op_iter():
            j4_sum += self.penalty.get(j_op.ID, (0, 0, 0))[2]

        self.QltList["J4"].append(j4_sum)

        # J5 показатель неравномерности загрузки ресурсов
        Nonuniformity = 0
        for clust in self.ClustList.values():
            for res in clust.ResList.values():
                Nonuniformity += (self.D - res.Fatigue) ** 2

        self.QltList["J5"].append(Nonuniformity / 2)
        if self.p:
            self.p.send("INF: Показатель неравномерности загрузки ресурсов: " + str(self.QltList["J5"][-1]))
        if PRINT:
            if self.QltList["J5"][0] > 0:
                print("J5 = ", self.QltList["J5"][-1], "\tнеравномерноть использования ресурсов")

        # J7 - время выполнения плана
        self.QltList["J7"].append(self.time - 1)
        if DEBUG_Q:
            if self.QltList["J7"][0] > 0:
                print("J7 = ", self.QltList["J7"][-1], "\tвремя выполнения плана ( ✕", self.QltList["J7"][0], ")")
        if False and self.logger:
            if self.QltList["J7"][0] > 0 and len(self.QltList["J7"]) != 3:
                self.logger.put({
                    "message": 'J7 = {} время выполнения плана ( ✕ {})'.format(self.QltList["J7"][-1],
                                                                               self.QltList["J7"][0]),
                    "variables": {
                        "quality_j7": [len(self.QltList["J7"]) - 2, self.QltList["J7"][-1]]
                    }

                })

        # J8
        self.QltList["J8"].append(0)
        # todo деление на 0

        # J9
        self.QltList["J9"].append(0)

        # J0
        genQlt = 0  # Обобщённый показатель качества
        for j, qlt in self.QltList.items():
            if j == "J0":
                continue
            genQlt += float(qlt[0] * qlt[
                -1])  # qlt[0] - коэффициент свёртки, qlt[-1] - частный показатель качества с последней итерации
        self.QltList["J0"].append(genQlt)

        if self.p:
            self.p.send("INF: Обобщённый показатель качества")
        if DEBUG_Q:
            print("J0 = ", self.QltList["J0"][-1], "\tобобщённый показатель качества")
        if self.logger:
            if len(self.QltList["J0"]) != 3:
                self.logger.put({
                    "message": "J0 = {} обобщённый показатель качества".format(self.QltList["J0"][-1], ),
                    "variables": {
                        "quality_j0": [len(self.QltList["J0"]) - 2, self.QltList["J0"][-1]],
                        "quality_j3": [len(self.QltList["J3"]) - 2, self.QltList["J3"][-1]],
                        "quality_j7": [len(self.QltList["J7"]) - 2, self.QltList["J7"][-1]]
                    }
                })

        # return (len(self.QltList["J0"]) >= 3 and abs(self.QltList["J0"][-1] - self.QltList["J0"][-2]) < e) or \
        return len(self.QltList["J0"]) > 6

        # если невязка обобщённого показателя больше e или если это только первая итерация
        # и не с чем сравнивать - повторить итерацию

    def calculate_transversality(self):
        """Расчёт начальных условий сопряжённой системы уравнений."""

        if DEBUG_TRANS:
            print("\nРасчёт условий трансверсальности")

        if self.p: self.p.send("INF: Расчёт условий трансверсальности")

        # расчёт невязок по операциям и потокам 𝜓
        for tr_proc in self.ProcList.values():
            for tr_op in tr_proc.OpList.values():
                # если работа не начинала выполняться, то она на либо на параллельной ветви,
                # либо предыдущая так и не завершилась из-за нехватки отведённого времени
                # в любом случае, эти операции не нужно учитывать следуя формулам
                # if tr_op.X == 0 and tr_op.XP == 0:
                if True:  # если мы исключаем из показателей качества оценку полноты выполнения, то и в условиях трансверсальности её нет
                    self.operation_conditions[tr_op.ID] = (self.D - tr_op.X) ** 2 * float(self.QltList['J7'][1]) + 2
                    self.stream_conditions[tr_op.ID] = (self.D - tr_op.XP) ** 2 * float(self.QltList['J7'][1]) + 2
                # else:
                #     self.operation_conditions[tr_op.ID] = (tr_op.A - tr_op.X) * float(self.QltList['J7'][1]) + 2
                #     self.stream_conditions[tr_op.ID] = (tr_op.AP - tr_op.XP) * float(self.QltList['J7'][1]) + 2
                # ОТКЛЮЧЕНО:
                # невязка умножается на коэффициент свёртки
                # добавляется двойка, так как операции с нулевым приоритетом никогда не выполняются
                # (не влияют на максимизацию Гамильтониана)
                # не единица, а двойка, так как при логарифмической нормировке log 1 = 0,
                # опять попадаем на нулевой приоритет

                # при единичной трансверсальности система нечувствительна к исходным данным и всегда выбирает один путь
                # 2019-10-08 В условия трансверсальности идут значения uv2 -
                # накопленные значения с начала интервала и до конца выполнения операции
                # смысл в том, что больший приоритет отдаётся работе, которая выполнялась позже других

        # расчёт неравномерности использования ресурсов
        # for clust in self.ClustList.values():
        #     for res in clust.ResList.values():
        #         self.resource_conditions[res.ID] = (self.D - res.Fatigue)  # * float(self.QltList[3][1]) + 2
        #         # невязка умножается на коэффициент свёртки

        # экспериментальный расчёт энергозатрат
        for clust in self.ClustList.values():
            for res in clust.ResList.values():
                self.resource_conditions[res.ID] = res.Fatigue * res.price if res.price else 0
                # невязка умножается на коэффициент свёртки
        max_cost = max(self.resource_conditions.items(), key=operator.itemgetter(1))[1]
        for clust in self.ClustList.values():
            for res in clust.ResList.values():
                self.resource_conditions[res.ID] = (max_cost - self.resource_conditions[res.ID]) * float(
                    self.QltList['J3'][1]) + 2
                # self.resource_conditions[res.ID] = 50 - res.price  # trying just plain price instead of complex indicator
                # (max_cost - self.resource_conditions[res.ID]) * float(
                # self.QltList['J3'][1]) + 2

        self.OpPriorMatrix = self.operation_conditions.copy()
        self.StreamPriorMatrix = self.stream_conditions.copy()
        self.ResPriorMatrix = self.resource_conditions.copy()

        if self.p:
            self.p.send("INF: Расчёт условий трансверсальности завершён")

        if DEBUG_TRANS:
            print("\t𝜓º")
            for pop, popv in self.OpPriorMatrix.items():
                print("\t\t", self.get_proc_op(pop)[1].Name, popv)
            print("\t𝜓ⁿ")
            for pop, popv in self.StreamPriorMatrix.items():
                print("\t\t", self.get_proc_op(pop)[1].Name, popv)
            print("\t𝜓ᴾ", self.ResPriorMatrix)

        if DEBUG_TRANS:
            print("*" * 30, " Условия трансверсальности ", "*" * 30)
            print(self.OpPriorMatrix)
            print(self.StreamPriorMatrix)

    def normalize_left(self):
        """
        Нормировка сопряжённых переменных для вывода их из отрицательной области
        :return: None
        """
        min_o = self.OpPriorMatrix[min(self.OpPriorMatrix, key=self.OpPriorMatrix.get)]
        if DEBUG_NORMALIZE:
            print("Нормировка по", min_o)
        for i, v in self.OpPriorMatrix.items():
            self.OpPriorMatrix[i] = log10(v - min_o + 2) if NORMALIZE_LOG_OP else v - min_o + 1
            if DEBUG_NORMALIZE:
                print(self.OpPriorMatrix[i])

        min_p = self.StreamPriorMatrix[min(self.StreamPriorMatrix, key=self.StreamPriorMatrix.get)]
        if DEBUG_NORMALIZE:
            print("Нормировка по", min_p)
        for i, v in self.StreamPriorMatrix.items():
            self.StreamPriorMatrix[i] = log10(v - min_p + 2) if NORMALIZE_LOG_ST else v - min_p + 1
            if DEBUG_NORMALIZE:
                print(self.StreamPriorMatrix[i])

    def reset_executed(self, clear_timetable=True, clear_restrictions=True):
        """Сброс состояния модели до начального.
        :param clear_timetable: очищать расписание
        :param clear_restrictions: очищать запреты на выполнение операций
        """
        for proc in self.ProcList.values():
            for op in proc.OpList.values():
                op.reset()

                # сброс врЕменных запретов на выполнение
                if clear_restrictions:
                    self.set_restriction(op.ID)
                    if DEBUG:
                        print("Сброс ограничений")
        for clust in self.ClustList.values():
            for res in clust.ResList.values():
                res.reset()

        if clear_timetable and len(self.timetable) > 0:
            self.timetable[-1].clear()

        for p in self.penalty:
            self.penalty[p] = (self.penalty[p][0], self.penalty[p][1], 0)

        self.debug_vars = {}

        if self.p:
            self.p.send("INF: Параметры модели инициализированы")

        if self.logger:
            self.logger.put({
                "message": 'Сброс состояний операций',
                "type": "command",
                "command": "reset_operations"
            })

    def reverse_integrate(self, tf=float('inf'), ts=0):
        """Полный обратный проход интегратора.
        :param tf: время начала обратного интегрирования, по умолчанию +inf
        :param ts: время окончания обратного интегрирования (tf > ts), по умолчанию 0
        """

        if DEBUG_REV:
            print("\nОбратное интегрирование")

        if self.p:
            self.p.send("INF: Старт обратного интегрирования от " + str(tf) + " до " + str(ts))

        ograph = {n[1].ID: list() for n in self.op_iter()}
        pgraph = {n[1].ID: list() for n in self.op_iter()}
        work = {n[1].ID: list() for n in self.op_iter()}

        self.time = min(tf, self.D)
        while self.time >= max(0, ts):
            if DEBUG_L1:
                print("\nВремя:", self.time)

            # обратное интегрирование со знаком минус
            # psi_main = psi_main - (
            # + SUM_on_predecessors ( SUM_on_resources ( psi_main_predecessor * epsilon_resource * tetha_predecessor +
            # + psi_resource +
            # + psi_stream_predecessor * c_stream_predecessor_resource ) ) * u_main_predecessor +

            # + SUM_on_successor (SUM_on_resources ( psi_main_successor * epsilon_resource * tetha_successor +
            # + psi_resource +
            # + psi_stream_successor * c_stream_successor_resource ) ) * u_main_successor ) )

            hr_status = {
                0: "ждёт начала выполнения",
                1: "выполняется",
                2: "завершена до отведённого времени",
                3: "завершена, отведённое время исчерпано",
                -1: "не выполнилась до конца отведённого времени",
                -2: "странный статус, возможна ошибка"
            }

            for proc in self.ProcList.values():
                for n in proc.graph.nodes():

                    # Вспомогательные сопряжённые переменные p
                    job_status = self.get_proc_op(n)[1].Status

                    # какой ресурс в какое время обслуживал операцию
                    timeline_dict = {t_time: t_res_id for (t_time, t_op_id), (t_res_id, t_intense)
                                     in self.timetable[-1].items() if t_op_id == n}
                    if timeline_dict:
                        max_time = max(timeline_dict, key=timeline_dict.get)
                        last_res_id = self.timetable[-1].get((max_time, n), [-1])[0]
                    else:
                        last_res_id = None

                    if DEBUG_REV:
                        print("\t" + self.get_proc_op(n)[1].Name, "[" + hr_status[job_status] + "], 𝜓º",
                              self.OpPriorMatrix[n],
                              ", 𝜓ⁿ", self.StreamPriorMatrix[n])
                        if last_res_id is not None:
                            print("\t\tПоследний задействованный ресурс", last_res_id)

                    # last_res_id - последний задействованный ресурс

                    # интегрирование сопряжённой системы уравнений основной модели

                    # Вспомогательные сопряжённые переменные p

                    # summa = self.OpPriorMatrix.get(n, 0)
                    summa_pred = summa_parallel = 0
                    for pred_op_id in proc.graph.predecessors(n):
                        for (clust, res) in self.res_iter():
                            # управление предшествующей операции
                            sm = (1 if res.ID == self.timetable[-1].get((self.time, pred_op_id), (-1, -1))[0] else 0) * \
                                 (self.OpPriorMatrix[pred_op_id] +
                                  self.ResPriorMatrix[res.ID] +
                                  self.StreamPriorMatrix[pred_op_id] *
                                  self.get_productivity(pred_op_id, res.ID))
                            if DEBUG_REV and sm != 0:
                                print("\t\tВклад предшествующей операции '", self.get_proc_op(pred_op_id)[1].Name,
                                      "' в 𝜓º:", sm, ", из них")
                                print("\t\t\t𝜓º", self.OpPriorMatrix[pred_op_id])
                                print("\t\t\t𝜓ᴾ", self.ResPriorMatrix[res.ID])
                                print("\t\t\t𝜓ⁿ✕c", self.StreamPriorMatrix[pred_op_id] *
                                      self.get_productivity(pred_op_id, res.ID))
                            summa_pred += sm
                        # учёт параллельно выполняемых операций (исключающее или)
                        for s in proc.graph.successors(
                                pred_op_id):  # для каждого предшественника пройти по всем последователям
                            if s == n: continue
                            # если группа 'fwd' соседней дуги совпадает с 'fwd' текущей дуги
                            if proc.graph.edges[pred_op_id, s]['fwd'] == proc.graph.edges[pred_op_id, n]['fwd']:
                                for (clust, res) in self.res_iter():
                                    sm = (1 if self.timetable[-1].get((self.time, s), (-1, -1))[
                                                   0] == res.ID else 0) * \
                                         (self.OpPriorMatrix[s] +
                                          self.ResPriorMatrix[res.ID] +
                                          self.StreamPriorMatrix[s] *
                                          self.get_productivity(s, res.ID))

                                    if DEBUG_REV and sm != 0:
                                        print("\t\tВклад параллельной операции '", self.get_proc_op(s)[1].Name,
                                              "' в 𝜓º", sm, "из них")
                                    summa_parallel += sm

                    # интегрирование сопряжённой системы уравнений потоковой модели
                    sum_stream = self.StreamPriorMatrix.get(n, 0)
                    for succ_op_id in proc.graph.successors(n):
                        for (clust, res) in self.res_iter():
                            # со знаком плюс, так как в уравнении стоит минус и проход в обратном направлении
                            sm = (1 if self.timetable[len(self.timetable) - 1].get((self.time, succ_op_id), (-1, -1))[0]
                                       == res.ID else 0) * \
                                 (self.OpPriorMatrix[succ_op_id] +
                                  self.ResPriorMatrix[res.ID] +
                                  self.StreamPriorMatrix.get(succ_op_id,
                                                             self.stream_init_conditions.get(succ_op_id, 0)) *
                                  self.get_productivity(succ_op_id, res.ID))

                            if DEBUG_REV and sm != 0:
                                print("\t\tВклад последующей операции '", self.get_proc_op(succ_op_id)[1].Name,
                                      "' в 𝜓ⁿ", sm, ", из них")
                                print("\t\t\t𝜓º", self.OpPriorMatrix[succ_op_id])
                                print("\t\t\t𝜓ᴾ", self.ResPriorMatrix[res.ID])
                                print("\t\t\t𝜓ⁿ✕c", self.StreamPriorMatrix[succ_op_id] *
                                      self.get_productivity(succ_op_id, res.ID))

                            sum_stream += sm

                    if NORMALIZE_LOG_ANGLE and (summa_pred + summa_parallel) > 1:
                        self.OpPriorMatrix[n] -= log10(summa_pred + summa_parallel)
                    else:
                        self.OpPriorMatrix[n] -= summa_pred + summa_parallel
                    ograph[n].append(self.OpPriorMatrix[n])

                    if NORMALIZE_LOG_ANGLE and (sum_stream) > 1:
                        self.StreamPriorMatrix[n] = log10(sum_stream)
                    else:
                        self.StreamPriorMatrix[n] = sum_stream

                    if DEBUG_REV:
                        print("\t\tИтого 𝜓º:", self.OpPriorMatrix[n],
                              "\t 𝜓ⁿ:", self.StreamPriorMatrix[n])

                    pgraph[n].append(self.StreamPriorMatrix[n])
                    work[n].append(
                        str(self.timetable[len(self.timetable) - 1][(self.time, n)][0]) if (self.time, n) in
                                                                                           self.timetable[
                                                                                               len(
                                                                                                   self.timetable) - 1] else '_')

            self.time -= self.Step

        # сохранение начальных условий сопряжённой системы уравнений
        self.operation_init_conditions = self.OpPriorMatrix.copy()
        self.stream_init_conditions = self.StreamPriorMatrix.copy()
        self.resource_init_conditions = self.ResPriorMatrix.copy()

        if DEBUG_REV:
            print('\tОсновной приоритет')
            for op, g in ograph.items():
                print('"' + "%s" % (self.get_proc_op(op)[1].Name,) + '"', end=": ")
                for p in g[::-1]:
                    print(round(p), end=", ")
                print()
            print('\tПотоковый приоритет')
            for op, g in pgraph.items():
                print('"' + "%s" % (self.get_proc_op(op)[1].Name,) + '"', end=": ")
                for p in g[::-1]:
                    print(round(p), end=", ")
                print()

        if DEBUG_REV:
            print('*' * 10, 'rew psi')
            for op, g in ograph.items():
                print('"' + "%s" % (self.get_proc_op(op)[1].Name,) + '"', end=": ")
                for p in g[::-1]:
                    print(round(p), end=", ")
                print()

            print('*' * 10, 'rew u')
            for op, g in work.items():
                # print '"' + "%s" % (self.get_proc_op(op)[1].Name,) + '"',
                for p in g[::-1]:
                    print(p, end=" ")
                print(self.get_proc_op(op)[0].Name, self.get_proc_op(op)[1].Name)

                '''
                for proc in self.ProcList.values():
                    for op in proc.OpList.values():
                        self.OpPriorMatrix[op] = log10(self.OpPriorMatrix[op] + 1)

                for clust in self.ClustList.values():
                    for res in clust.ResList.values():
                        self.ResPriorMatrix[op] = log10(self.ResPriorMatrix[res] + 1)
                '''
        if self.p:
            self.p.send("INF: Обратное интегрирование завершено")
        pass

    def execute_plan(self, ts=0, tf=float('inf')):
        """Имитация выполнения плана по имеющемуся расписанию.
        :param ts: начало интервала имитации
        :param tf: конец интервала имитации, включительно
        """
        if PRINT or DEBUG or DEBUG_L1:
            self.ograph = {n[1].ID: list() for n in self.op_iter()}
            self.pgraph = {n[1].ID: list() for n in self.op_iter()}
            self.work = {n[1].ID: list() for n in self.op_iter()}

        self.reset_executed(clear_timetable=False, clear_restrictions=False)  # сбросить текущее состояние модели
        self.OpPriorMatrix = self.operation_init_conditions.copy()
        self.StreamPriorMatrix = self.stream_init_conditions.copy()
        self.ResPriorMatrix = self.resource_init_conditions.copy()

        if len(self.timetable) == 0:
            return
        crop_timetable = {}  # сокращённая версия расписания, только на заданный участок воспроизведения
        t_fin = tf
        # t_fin = min(tf, self.D)
        for proc in self.ProcList.values():  # по всем процессам
            for job in proc.OpList.values():  # по всем опрерациям в процессе
                # пропуск работ с нулевой длительностью (старт/стоп, ветвления и т.д.)
                if job.A == 0: continue
                # self.Schedule[(proc, job)] = []  # список словарей start stop res intens
                t = ts
                while t <= t_fin:  # пробег по временной шкале и поиск триггеров выполнения операций
                    # TODO: перенести этот цикл в параллельные вычисления - Workers
                    if (t, job.ID) in self.timetable[-1]:  # выполняется ли работа на текущем временном шаге
                        # запомним ресурс, на котором выполняется работа
                        res_id = self.timetable[-1][(t, job.ID)][0]
                        # запомним интенсивность, с которой выполняется работа
                        intens = self.timetable[-1][(t, job.ID)][1]
                        res = self.get_clust_res(res_id)[1]
                        # постановка операции на ресурс согласно расписанию
                        res.load_operation(job, intens)
                        # заполняем новое расписание, которое не будет включать время ветвления
                        crop_timetable[(t, job.ID)] = (res_id, intens)
                        res.Release()  # снять нагрузку на ресурс перед сдвигом времени
                        if PRINT:
                            print(t, "операция", job.ID, "на", res_id, "с интенсивностью", intens)

                            # восстанавливаются приоритеты (необходимо для случая продолжения планирования)
                            # self.calculate_priorities(t)
                    t += 1

        # расписание режется до заданного временнОго участка
        self.timetable[-1] = crop_timetable.copy()

        t = ts
        while t <= t_fin:  # пробег по временной шкале и расчёт приоритетов по усечённому расписанию
            self.calculate_priorities(t)
            t += 1

        # устанавливается текущее время модели - "оперативный скачок во времени"
        self.time = t_fin

        if DEBUG:
            print('*' * 10, 'fwd u')
            for mt in range(0, int(self.D) - 1):
                sys.stdout.write(str(mt).zfill(2))
            print()
            for op, g in sorted(self.work.items(), key=lambda k: k[0]):
                # print '"' + str(self.get_proc_op(op)[1].ID) + '"',
                for p in g:
                    print(p, end=" ")
                # print self.OpPriorMatrix[op]
                print(self.get_proc_op(op)[1].Name, self.OpPriorMatrix.get(op, None), self.get_proc_op(op)[1].ID)

    def calculate_plan(self, options=None):
        """Процесс расчёта расписания.
        :param options: параменты расчётов:
                        method: алгоритм поиска решения (FIFO, LIFO, PULP), default = FIFO
                        relaxed: снятие ограничений на неразрывность операций, default = False
                        debug_tab: отступы для рекурсии
        """
        ####
        ## PAVLOV: искуственный ограничитель на число итераций...
        # global i
        # if i > 10:
        #    pass
        #    #return
        # insp[i] = inspect.stack()[1][2]
        # i += 1
        ####
        if DEBUG_L1:
            print("Расчёт плана")

        if self.logger:
            self.logger.put({"message": "Начало расчёта", "type": "log"})

        integrate_options = dict(method='FIFO', relaxed=False, debug_tab=0)
        if options is not None:
            integrate_options['method'] = options.get('method', 'FIFO')
            integrate_options['relaxed'] = options.get('relaxed', False)
            integrate_options['debug_tab'] = options.get('debug_tab', 0)

        # if DEBUG_L1:
        #     print('Построение нулевого решения ' + (
        #         '(релаксированная задача)' if integrate_options['relaxed'] else ''))

        # интегрирование диспетчерского решения с запретами на прерывание в прямом направлении
        # if not integrate_options.get('relaxed', False):
        #     self.integrate(0, self.D, dict(method="NONE", relaxed=integrate_options.get('relaxed', False)))
        #     self.Assess()

        if DEBUG_L1:
            print('Построение диспетчерского решения ' + (
                '(релаксированная задача)' if integrate_options['relaxed'] else ''))

        if self.logger:
            self.logger.put({"type": "log", "message": "Построение диспетчерского решения " + (
                '(релаксированная задача)' if integrate_options['relaxed'] else '')})

        # TODO: Update integrate_options

        # интегрирование диспетчерского решения с запретами на прерывание в прямом направлении
        self.integrate(0, self.D, dict(debug_tab=integrate_options['debug_tab'], method="FIFO",
                                       relaxed=integrate_options.get('relaxed', False)))
        self.Assess()

        if self.logger:
            self.logger.put({"type": "log", "message": 'Построение диспетчерского решения завершено'})

        self.reset_executed(clear_timetable=False,
                            clear_restrictions=not integrate_options['relaxed'])

        if integrate_options['method'] != 'PULP':
            if DEBUG:
                print("_" * 60)
                for q in self.QltList:
                    for i in q: print(i, "\t", end=' ')
                    print()
                    # END DEBUG
            return

        # стартуем с нулевым решением
        self.integrate(0, self.D, dict(debug_tab=integrate_options['debug_tab'], method="NULL",
                                       relaxed=integrate_options.get('relaxed', False)))

        self.Assess()

        self.iteration = 0
        self.conflict_count = 0

        # PAVLOV: добавить отлов по времени (на расчеты, не модельное)
        while True:
            # PAVLOV: здесь добавка не спасает от биений, зацикливание где-то внутри
            # if self.iteration > 0: break
            if DEBUG:
                print("_" * 60)
                for q in self.QltList:
                    for i in q: print('{0:9}'.format(i, ), )

                    # for i in q: print i,
                    print()

            if self.logger:
                self.logger.put({
                    "message": 'Итерация {}'.format(self.iteration, ),
                    "variables": {
                        "iteration": self.iteration
                    },
                    "type": "log"
                })

            # END DEBUG

            self.calculate_transversality()
            self.reverse_integrate(self.D, 0)
            self.reset_executed(clear_timetable=False,
                                clear_restrictions=not integrate_options['relaxed'])

            # очищать запреты на исполнение только в основном прогоне.
            # При решении релаксированных задач запреты сохранять
            if PRINT:
                print("*" * 20, "conjunctive initial conditions")
                for k, v in self.operation_init_conditions.items():
                    print(k, v)

            # self.normalize_left()
            from copy import copy
            integrate_options2 = copy(integrate_options)
            integrate_options2['debug_tab'] = integrate_options['debug_tab'] + 1
            self.integrate(0, self.D, integrate_options2)  # оптимизация плана

            if self.p: self.p.send('VAL: ' + str(self.QltList[0][-1]))
            # в pipe отправляем показатель качества

            if self.logger:
                self.logger.put({"type": 'log', 'message': 'Окончание итерации {}'.format(self.iteration, )})

            if len(self.QltList["J0"]) > (1 if integrate_options['relaxed'] else 3):
                if self.p: self.p.send("CMD: stop")
                self.Assess()
                break

            # # DEBUG
            #
            #			print ("Расписание:")
            #
            #			for t in range(int(Dyn.D)):
            #				print "Время: " + str(t)
            #				for proc in Dyn.ProcList.values():
            #					for op in proc.OpList.values():
            #						if (t, op) in Dyn.timetable:
            #							print op.ID,
            #							print Dyn.OpPriorMatrix[op],
            #							print str(op.X) + " -> " + str(op.A)
            #
            #			if raw_input() == "b": break
            #
            #			# END DEBUG

            # self.Assess()
            if self.Assess(): break

            # if not integrate_options['relaxed']:
            #     break

            self.iteration += 1

        self.reset_executed(clear_timetable=False,
                            clear_restrictions=not integrate_options['relaxed'])

        if self.p: self.p.send("CMD: stop")
        if self.logger:
            self.logger.put({"message": "Расчёт окончен", "type": "log"})

        if DEBUG_Q:
            print("Расчёт окончен")

        # запись результатов последней оптимизации для Захарова
        # writer = csv.writer(ham_file, dialect='excel', delimiter=';')
        # writer.writerows(csv_data)
        # ham_file.close()

    # в pipe отправляем признак завершения оптимизации

    def SaveGanttXML(self, outfilename):
        """Создание исходных данных для dhtmlxGantt"""

        dataXML = etree.Element('data')
        doc = etree.ElementTree(dataXML)
        now = datetime.now()
        procStart = {}
        procEnd = {}

        # заготовка для определения истиных временнЫх рамок процесса: старт в конце, конец - в начале интервала планирования
        for proc in self.ProcList.values():
            procStart[proc] = now + timedelta(minutes=int(self.D))
            procEnd[proc] = now

        # упорядочивание операций в соответствии с графом

        def add_scsr(gnt, proc, op_id):
            op = proc.get_op(op_id)
            if not (proc, op) in gnt:
                gnt.append((proc, op))
            for scsr in proc.graph.successors_iter(op_id):
                add_scsr(gnt, proc, scsr)

        gantt_list = list()

        for proc in self.ProcList.values():

            # определяем начальные и конечные узлы
            start_nodes = list()
            end_nodes = list()
            for node in proc.graph.nodes():
                if not proc.graph.predecessors(node):
                    start_nodes.append(node)
                if not proc.graph.successors(node):
                    end_nodes.append(node)

            #
            for start_node in start_nodes:
                add_scsr(gantt_list, proc, start_node)

        # for proc in self.ProcList.values():
        #
        #     start_nodes = list()
        #     end_nodes = list()
        #     for node in proc.graph.nodes_iter():
        #         if not proc.graph.predecessors(node):
        #             start_nodes.append(node)
        #         if not proc.graph.successors(node):
        #             end_nodes.append(node)
        #     mutations = [zip(x,start_nodes) for x in permutations(start_nodes,len(end_nodes))]
        #
        #     for path in nx.all_simple_paths(proc.graph, source=0, target=3):

        for proc, job in gantt_list:
            if not (proc, job) in self.Schedule:
                continue
            # по всем фрагментам исполнения операции
            for i, j in zip(self.Schedule[(proc, job)], range(len(self.Schedule[(proc, job)]))):
                start = now + timedelta(days=int(i.get('start', 0)))
                stop = now + timedelta(days=int(i.get('stop', 0)))

                # if DEBUG:
                #    print("_ " * i.get('start', 0), "|" * i.get('stop', 0))

                task = etree.SubElement(dataXML, 'task', id=str(job.ID),
                                        start_date=start.strftime('%d-%m-%Y %H:%M'), duration=str(int(ceil(job.A))),
                                        progress=str(job.X / job.A), end_date=stop.strftime('%d-%m-%Y %H:%M'),
                                        parent=str(proc.ID))
                task.text = job.Name

                etree.SubElement(task, 'holder').text = i['res'].Name
                etree.SubElement(task, 'identificator').text = str(job.ID) + str(j)
                # etree.SubElement(task, 'priority').text =

                # расширяем левую и правую границы процесса, проверяя каждую операцию
                # print 'start:', now + timedelta(minutes = int(i['start'])), procStart[proc], min(now + timedelta(minutes = int(i['start'])), procStart[proc])
                procStart[proc] = min(now + timedelta(days=int(i['start'])), procStart[proc])
                # print 'stop:', now + timedelta(minutes = int(i['stop'])), procEnd[proc], max(now + timedelta(minutes = int(i['stop'])), procEnd[proc])
                procEnd[proc] = max(now + timedelta(days=int(i.get('stop', 0))), procEnd[proc])

        # создание агрегированных процессов
        for proc in self.ProcList.values():
            processTask = etree.SubElement(dataXML, 'task', id=str(proc.ID),
                                           start_date=procStart[proc].strftime('%d-%m-%Y %H:%M'),
                                           end_date=procEnd[proc].strftime('%d-%m-%Y %H:%M'))
            processTask.text = proc.Name

            etree.SubElement(processTask, 'holder').text = proc.Name
            etree.SubElement(processTask, 'identificator').text = str(proc.ID)

        # создание связей операций
        opLinks = etree.SubElement(dataXML, 'coll_options', {'for': 'links'})

        for proc in self.ProcList.values():
            for n in proc.graph.edges():
                linkItem = etree.SubElement(opLinks, 'item', id=str(uuid1()),
                                            source=str(n[0]),
                                            target=str(n[1]),
                                            type='0')

        outFile = open(outfilename, 'wb')
        doc.write(outFile, xml_declaration=True, encoding='utf-8')

        """
            <data>
                <task id='1' parent='' start_date='01-04-2013 00:00' open='true' progress='0.4' end_date='01-04-2013 00:18'>
                    <holder><![CDATA[Mike]]></holder>
                    <priority><![CDATA[High]]></priority>
                    <![CDATA[Project #2]]>
                </task>
                <task id='2' parent='1' start_date='01-04-2013 13:00' duration='8' progress='0.6' end_date='01-04-2013 13:08'>
                    <holder><![CDATA[John]]></holder>
                    <priority><![CDATA[Medium]]></priority>
                    <![CDATA[Task #1]]>
                </task>
                <task id='3' parent='1' start_date='01-04-2013 12:00' duration='8' progress='0.6' end_date='01-04-2013 12:08'>
                    <holder><![CDATA[Alex]]></holder>
                    <priority><![CDATA[Low]]></priority>
                    <![CDATA[Task #2]]>
                </task>
                <coll_options for='links'>
                    <item id='1' source='1' target='2' type='1' />
                    <item id='2' source='2' target='3' type='0' />
                    <item id='3' source='3' target='4' type='0' />
                    <item id='4' source='2' target='5' type='2' />
                </coll_options>
            </data>
        """

    def SaveScheduleXML(self, outfilename):
        """Создание XML структуры с результатами"""

        dataXML = etree.Element('data')
        doc = etree.ElementTree(dataXML)
        now = datetime.now()
        procStart = {}
        procEnd = {}

        # заготовка для определения истиных временнЫх рамок процесса: старт в конце, конец - в начале интервала планирования
        for proc in self.ProcList.values():
            procStart[proc] = now + timedelta(minutes=int(self.D))
            procEnd[proc] = now

        # упорядочивание операций в соответствии с графом

        def add_scsr(gnt, proc, op_id):
            op = proc.get_op(op_id)
            if not (proc, op) in gnt:
                gnt.append((proc, op))
            for scsr in proc.graph.successors_iter(op_id):
                add_scsr(gnt, proc, scsr)

        gantt_list = list()

        for proc in self.ProcList.values():

            # определяем начальные и конечные узлы
            start_nodes = list()
            end_nodes = list()
            for node in proc.graph.nodes():
                if not proc.graph.predecessors(node):
                    start_nodes.append(node)
                if not proc.graph.successors(node):
                    end_nodes.append(node)

            #
            for start_node in start_nodes:
                add_scsr(gantt_list, proc, start_node)

        # for proc in self.ProcList.values():
        #
        #     start_nodes = list()
        #     end_nodes = list()
        #     for node in proc.graph.nodes_iter():
        #         if not proc.graph.predecessors(node):
        #             start_nodes.append(node)
        #         if not proc.graph.successors(node):
        #             end_nodes.append(node)
        #     mutations = [zip(x,start_nodes) for x in permutations(start_nodes,len(end_nodes))]
        #
        #     for path in nx.all_simple_paths(proc.graph, source=0, target=3):

        for proc, job in gantt_list:
            if not (proc, job) in self.Schedule:
                continue
            # по всем фрагментам исполнения операции
            for i, j in zip(self.Schedule[(proc, job)], range(len(self.Schedule[(proc, job)]))):
                start = now + timedelta(days=int(i.get('start', 0)))
                stop = now + timedelta(days=int(i.get('stop', 0)))

                # if DEBUG:
                #     print "_ " * i.get('start', 0), "|" * i.get('stop', 0)

                task = etree.SubElement(dataXML, 'task', id=str(job.ID),
                                        start_date=start.strftime('%d-%m-%Y %H:%M'), duration=str(int(ceil(job.A))),
                                        progress=str(job.X / job.A), end_date=stop.strftime('%d-%m-%Y %H:%M'),
                                        parent=str(proc.ID))
                task.text = job.Name

                etree.SubElement(task, 'holder').text = i['res'].Name
                etree.SubElement(task, 'identificator').text = str(job.ID) + str(j)
                # etree.SubElement(task, 'priority').text =

                # расширяем левую и правую границы процесса, проверяя каждую операцию
                # print 'start:', now + timedelta(minutes = int(i['start'])), procStart[proc], min(now + timedelta(minutes = int(i['start'])), procStart[proc])
                procStart[proc] = min(now + timedelta(days=int(i['start'])), procStart[proc])
                # print 'stop:', now + timedelta(minutes = int(i['stop'])), procEnd[proc], max(now + timedelta(minutes = int(i['stop'])), procEnd[proc])
                procEnd[proc] = max(now + timedelta(days=int(i.get('stop', 0))), procEnd[proc])

        # создание агрегированных процессов
        for proc in self.ProcList.values():
            processTask = etree.SubElement(dataXML, 'task', id=str(proc.ID),
                                           start_date=procStart[proc].strftime('%d-%m-%Y %H:%M'),
                                           end_date=procEnd[proc].strftime('%d-%m-%Y %H:%M'))
            processTask.text = proc.Name

            etree.SubElement(processTask, 'holder').text = proc.Name
            etree.SubElement(processTask, 'identificator').text = str(proc.ID)

        # создание связей операций
        opLinks = etree.SubElement(dataXML, 'coll_options', {'for': 'links'})

        for proc in self.ProcList.values():
            for n in proc.graph.edges():
                linkItem = etree.SubElement(opLinks, 'item', id=str(uuid1()),
                                            source=str(n[0]),
                                            target=str(n[1]),
                                            type='0')

        outFile = open(outfilename, 'wb')
        doc.write(outFile, xml_declaration=True, encoding='utf-8')

        """
            <schedule>
                <processes>
                    <process id="1">
                        <operation id="1">
                            <name>Погрузка элемента №3 на платформу</name>
                            <priority>0.3254</priority>
                            <resource>RS_2</resource>
                            <start>
                                <time intensity="5">12</time>
                                <time intensity="3">24</time>
                            </start>
                            <end>
                                <time>15</time>
                                <time>25</time>
                            </end>
                        </operation>
                        <operation id="2">
                            <name>Транспортировка элемента №3</name>
                            <priority>0.3254</priority>
                            <resource>RS_3</resource>
                            <start>
                                <time intensity="7">0</time>
                                <time intensity="7">16</time>
                                <time intensity="2">26</time>
                            </start>
                            <end>
                                <time>11</time>
                                <time>23</time>
                                <time>31</time>
                            </end>
                        </operation>
                    </process>
                </processes>
                <quality>
                    <pki id="J0" generalized="true">
                        <name>обобщённый показатель качества</name>
                        <val>270.0</val>
                    </pki>
                    <pki id="J1">
                        <weight>0.8</weight>
                        <name>Затраты энергии</name>
                        <val>321</val>
                    </pki>
                    <pki id="J2">
                        <weight>0.2</weight>
                        <name>Затраты времени</name>
                        <val>31</val>
                    </pki>
                </quality>
                <resources>
                    <resource id="RS_2">
                        <worktime>12</worktime>
                    </resource>
                    <resource id="RS_3">
                        <worktime>16</worktime>
                    </resource>
                </resources>
            </schedule>
        """

    def SaveListXML(self, outfilename):
        """Создание исходных данных для dhtmlxList"""

        pki_names = {
            'J0': u'обобщённый показатель качества',
            'J1': u'невязка по времени выполнения',
            'J2': u'невязка по потоку',
            'J3': u'качество выполнения операций (𝜂-функция)',
            'J4': u'штрафы за нарушения директивных сроков (q-функция)',
            'J5': u'неравномерность загрузки ресурсов',
            'J6': u'разрывность операций',
            'J7': u'количество завершённых процессов',
            'J8': u'количество завершённых операций',
            'J9': u'показатель робастности'
        }

        dataXML = etree.Element('data')
        doc = etree.ElementTree(dataXML)

        for i, pki in self.QltList.items():
            ind = etree.SubElement(dataXML, 'item', id=str(i))

            etree.SubElement(ind, 'pki_name').text = pki_names[i]
            etree.SubElement(ind, 'pki_val').text = str(pki[-1])

        outFile = open(outfilename, 'wb')
        doc.write(outFile, xml_declaration=True, encoding='utf-8')

        """
        <data>
            <item id="J0">
                <pki_name>обобщённый показатель качества</pki_name>
                <pki_val>270.0</pki_val>
            </item>
            <item id="J1">
                <pki_name>невязка по времени выполнения</pki_name>
                <pki_val>0.0</pki_val>
            </item>
        </data>
        """

    def SaveChartXML(self, outfilename):
        """Создание исходных данных для dhtmlxChart"""

        dataXML = etree.Element('data')
        doc = etree.ElementTree(dataXML)

        # Сортировка ресурсов по убыванию времени задействования
        reses = sorted([res for clus, res in self.res_iter()], key=lambda rs: rs.Fatigue, reverse=True)
        for i, res in enumerate(reses):
            if res.Fatigue != 0:
                ind = etree.SubElement(dataXML, 'item', id=str(i))

                etree.SubElement(ind, 'res_name').text = res.Name
                etree.SubElement(ind, 'res_fat').text = str(res.Fatigue)

        outFile = open(outfilename, 'wb')
        doc.write(outFile, xml_declaration=True, encoding='utf-8')


        """
            <data>
               <item id="1">
                   <sales>7.3</sales>
                   <year>2008</year>
               </item>
               <item id="2">
                   <sales>7.6</sales>
                   <year>2009</year>
               </item>
            </data>
        """

    def BuildSchedule(self, iteration=0):
        """Создание итогового расписания с интервалами в непрерывном времени"""
        iteration -= 1  # в timetable первая итерация имеет номер 0, а в Quality - номер 1
        if len(self.timetable) == 0 or not sum([len(k) for k in self.timetable]): return
        t = 0
        for proc in self.ProcList.values():  # по всем процессам (values более экономичен к памяти по сравнению с values)
            # pydevd.settrace('macmini')
            for job in proc.OpList.values():  # по всем опрерациям в процессе
                # пропуск работ с нулевой длительностью (старт/стоп, ветвления и т.д.)
                if job.A == 0: continue
                self.Schedule[(proc, job)] = []  # список словарей start stop res intens
                t = 0
                JobRun = 0  # выполняется ли работа на предыдущем временном шаге
                WasOnRes = None  # на каком ресурсе выполнялась работа на предыдущем временном шаге
                WasIntens = 0  # интенсивность выполнения на предыдущем шаге
                while t <= max([k[0] for k in self.timetable[iteration].keys()]) + 1:
                    # пробег по временной шкале и поиск триггеров выполнения операций
                    # заглядываем на 1 такт вперёд для завершения последней операции
                    # TODO: перенести этот цикл в параллельные вычисления - Workers
                    if (t, job.ID) in self.timetable[iteration]:  # выполняется ли работа на текущем временном шаге
                        JobNow = 1
                        OnRes = self.timetable[iteration][(t, job.ID)][
                            0]  # запомним ресурс, на котором выполняется работа
                        Intens = self.timetable[iteration][(t, job.ID)][
                            1]  # запомним интенсивность, с которой выполняется работа
                    else:
                        JobNow = 0
                        OnRes = None
                        Intens = 0

                    if JobNow == 1 and JobRun == 1 and (
                            OnRes != WasOnRes or WasIntens != Intens):  # остановим работы, у которых нашли изменения режима работы
                        self.Schedule[(proc, job)][-1]['stop'] = t

                    if (JobNow == 0 and JobRun == 1):  # остановим работы, которые не выполняются
                        self.Schedule[(proc, job)][-1]['stop'] = t

                    # TODO: при смене интенсивности выполнения также прерывать работу
                    if JobNow == 1 and (
                            JobRun == 0 or OnRes != WasOnRes or WasIntens != Intens):  # работа начала выполняться или продолжила выполняться на другом ресурсе или с другой интенсивностью
                        JobRun = 1
                        WasOnRes = OnRes  # запомним для следующего временного шага
                        WasIntens = Intens  # запомним для следующего временного шага
                        self.Schedule[(proc, job)].append({'start': t, 'res': self.get_clust_res(OnRes)[1],
                                                           'intens': self.timetable[iteration][(t, job.ID)][1]})

                    if JobNow == 0:
                        JobRun = 0  # запомним для следующего временного шага
                        WasOnRes = None  # запомним для следующего временного шага
                        WasIntens = 0  # запомним для следующего временного шага
                    else:
                        JobRun = 1

                    t += self.Step
        return t

    def DetectAnyTime(self):
        """Определение лучшего решения при отсутствии сходимости итерационной процедуры"""
        if len(self.QltList['J0']) > 2:
            return min(enumerate(self.QltList['J0'][3:]), key=operator.itemgetter(1))[0] + 3
        else:
            return 1  # PAVLOV: нулевая итерация возвращает 1.0


class UniProcess(object):
    """Класс универсального процесса."""
    ProcID = 0

    def __init__(self, pname, pid=None):
        """Конструктор процесса.
        :param pname: отображаемое имя процесса,
        :param pid: идентификатор процесса, по умолчанию None.
        """
        if pid:
            self.ID = str(pid)
            # UniProc.ProcID = int(pid) + 1  # нужен механизм анализа на непересекающиеся индексы
        else:
            self.ID = str(uuid1())  # UniProc.ProcID  # Автоинкремент сквозного идентификатора
            # UniProc.ProcID = UniProc.ProcID + 1

        self.Name = pname
        self.OpList = {}  # Список операций в процессе. В виде словаря для удобной работы со сквозными индексами
        # self.OpList['_init'] = первая операция в процессе. Обязательно к заполнению!

        self.graph = nx.DiGraph()  # альтернативный граф операций

    def add_operation(self, opname, a, ap, opid=None, tempid=None, x=None, y=None):
        """Добавление операции в процесс. Возвращает объект операцию.
        :param opname: отображаемое имя
        :param a: длительность
        :param ap: объём информации в операции
        :param opid: идентификатор операции, по умолчанию None
        :param tempid: идентификатор операции в файле шаблона, по умолчанию None
        :return newop: объект новой операции
        """
        newop = UniOp(opname, a, ap, opid, tempid, x, y)

        # if not len(self.OpList):
        #	self.OpList["_init"] = newop			# обязательно указать, какая операция будет первой; доступ к остальным через ссылку UniOp.Next
        # знак подчёркивания в начале для правильной сортировки
        # else:
        #	pass
        #

        self.OpList[newop.ID] = newop

        # pydevd.settrace('macmini')
        self.graph.add_node(newop.ID, data=newop.ID)  # добавляем узел графа

        return newop

    def DelOp(self, op_id):
        """Удаление операции из процесса по её индексу"""
        self.graph.remove_node(op_id)

    def get_op(self, op_id):
        """Получение операции по её номеру"""
        return self.OpList[op_id] if op_id in self.OpList else None

    def add_link(self, from_op, to_op, fwd_group=1, rev_group=1):
        """Добавление связи между операциями. Одинаковые fwd_group (или rev_group) объединяются исключающим ИЛИ, а разные - И
        PAVLOV: из каждой группы должны выполниться ровно 1 операция (группы - это номера fwd и rev)
        """
        self.graph.add_edge(from_op, to_op, fwd=fwd_group, rev=rev_group)
        pass

    def remove_link(self, from_op, to_op):
        "Удаление связи между операциями"
        self.graph.remove_edge(from_op, to_op)
        pass


class UniOp(object):
    "Класс универсальной операции"
    OpID = 0  # внутренний счётчик максимального индекеса

    def __init__(self, opname, a, ap, opid=None, template_id=None, node_x=None, node_y=None):
        "opname - отображаемое имя, a - длительность операци, ap - объём информации в операции, x - выполненная длительность, xp - обработаненый поток"

        # TODO: сделать возможность вставки в произвольное место цепочки

        if opid:
            self.ID = str(opid)
            # UniOp.OpID = int(opid) + 1

        # TODO: нужен механизм анализа на непересекающиеся индексы

        else:
            self.ID = str(uuid1())  # UniOp.OpID  # Автоинкремент сквозного идентификатора
            # UniOp.OpID = UniOp.OpID + 1

        self.template_id = str(template_id)
        self.Name = opname
        self.A = a and float(a)
        self.AP = ap and float(ap)
        self.X = 0
        self.XP = 0
        self.Previous = None
        self.Next = None
        self.Status = OP_WAIT
        self.node_x = node_x
        self.node_y = node_y

    def execute(self, d=None, i=1):
        """Выполнение операции.
        :param d: длительность выполнения
        :param i: интенсивность выполнения (объём обработанного потока)
        :return status: возвращает статус операции
        """

        if d:
            self.X = min(self.X + d, self.A)
            self.XP = min(self.XP + i, self.AP)
        else:
            self.X = self.A  # выполнение полностью
            self.XP = self.AP  # по времени и потоку

        if self.X >= self.A and self.XP < self.AP:
            # Palich test (замена OP_TIMEOUT на OP_EXEC ниже по коду) - МОДЕЛЬ РАБОТАЕТ КАК ЧАСЫ
            self.Status = OP_EXEC  # отведенное время вышло (не нашлось ресурса, который бы выполнил операцию в срок, будем нарушать)
            # self.Status = OP_TIMEOUT  # не выполнилась до конца отведённого времени
            if PRINT:
                print("Операция", self.Name, "не выполнилась до конца отведённого времени")
        elif self.X < self.A and self.XP >= self.AP:
            self.Status = OP_FLOW_COMPLETED  # завершена до отведённого времени
            # self.X = self.A
            if PRINT:
                print("Операция", self.Name, "завершена до отведённого времени")
        elif self.X >= self.A and self.XP >= self.AP:
            self.Status = OP_COMPLETED  # завершена, отведённое время исчерпано
            if PRINT:
                print("Операция", self.Name, "завершена, отведённое время исчерпано")
        elif self.X > 0 and self.XP > 0:
            self.Status = OP_EXEC  # выполняется
            if PRINT:
                # print "Операция", self.ID, "выполняется"
                pass
        elif self.X == 0 and self.XP == 0:
            self.Status = OP_WAIT  # ждёт начала выполнения
            if PRINT:
                print("Операция", self.Name, "ждёт начала выполнения")
        else:
            self.Status = OP_STRANGE  # странный статус
            if PRINT:
                print("Операция", self.Name, "в странном состоянии")

        return self.Status

    def reset(self, a=0, ap=0, x=0, xp=0):
        """Сбросить состояние операции до a (длительность), ap (объём данных), x (наработка по времени), xp (наработка по потоку). По умолчанию сброс до 0"""
        # TODO: отказаться от сброса в ненулевые значения
        self.X = x
        self.XP = xp
        self.Status = OP_WAIT  # ждёт начала выполнения

    def ExeQlt(self, t):
        """Посчитать значение функции качества в момент времени t"""
        pass

    def Rest(self):
        "Вернуть невязки по длительности и объёму данных в операции"
        pass


class UniClust(object):
    """Класс универсального кластера"""
    ClustID = 0

    def __init__(self, cname, bw=0, cid=None):
        "Конструктор кластера. came - отображаемое имя, bw - bandwidth - пропускная способность кластера"
        if cid:
            self.ID = str(cid)
            # UniClust.ClustID = int(cid) + 1  # нужен механизм анализа на непересекающиеся индексы
        else:
            self.ID = str(uuid1())  # UniClust.ClustID  # Автоинкремент сквозного идентификатора
            # UniClust.ClustID = UniClust.ClustID + 1

        self.Name = cname
        self.Bandwidth = float(bw)  # пропускная способность кластера
        self.ResList = {}  # Список ресурсов в кластере. В виде словаря для удобной работы со сквозными индексами

    def AddRes(self, rname, mi, thrds=1, price=0, rid=None, tid=None):
        """ Добавление ресурса в модель. Возвращает созданный ресурс.
            rname - наименование
            maxi - максимальная суммарная производительность ресурса
            threads - число параллельных исполнителей [1]
            price - стоимость единицы производительности ресурса [0]
            resid - идентификатор ресурса [автогенерирование]
            tid - идентификатор в файле-шаблоне [None]
        """
        newres = UniRes(rname, mi, thrds, price, rid, tid)
        self.ResList[newres.ID] = newres
        return newres

    def DelRes(self, op):
        """Удаление ресурса из кластера"""
        pass


class UniRes(object):
    "Класс универсального ресурса"
    ResID = 0

    def __init__(self, resname, maxi, threads=1, price=0, resid=None, template_id=None):
        """
        :param resname: имя ресурса
        :param maxi: максимальная суммарная производительность ресурса
        :param threads: число параллельных исполнителей
        :param price: стоимость единицы времени ресурса
        :param resid: идентификатор ресурса
        :param template_id: шаблонный идентификатор ресурса
        """
        if resid:
            self.ID = str(resid)
            # UniRes.ResID = int(resid) + 1
        else:
            self.ID = str(uuid1())  # UniRes.ResID  # Автоинкремент сквозного идентификатора
            # UniRes.ResID = UniRes.ResID + 1

        self.template_id = str(template_id)

        self.Name = resname

        # исключаем None из входных параметров (added by Palich)
        if maxi is None:
            self.MaxIntense = 10 ** 6
        else:
            self.MaxIntense = maxi and float(maxi)

        if threads is None:
            self.MaxThreads = 1
        else:
            self.MaxThreads = threads and int(threads)

        if price is None:
            self.price = 0
        else:
            self.price = price and float(price)  # цена использования единицы мощности ресурса в единицу времени

        self.Threads = 0
        self.Payload = 0
        self.Fatigue = 0  # "Усталость" ресурса - общее время наработки
        self.cost = 0  # общая стоимость использования ресурса

    def test_load(self, op, i=1):
        """Протестировать, может ли ресурс принять операцию в обработку.
        :param op: операция
        :param i: интенсивность выполнения
        :return status: результат тестирования (RES_REJECTED, RES_PROCESSING)
        """
        # если ресурс занят полностью, операция не сможет выполниться
        if self.Threads >= self.MaxThreads or self.Payload >= self.MaxIntense:  # тестируем вычислитель и максимальную производительность
            return RES_REJECTED
        # если запуск новой операции займёт ресурс полностью - сообщим об этом
        elif self.Threads + 1 >= self.MaxThreads or self.Payload + i >= self.MaxIntense:
            return RES_TO_FULL
        # если ресурс после загрузки новой работой будет в состоянии принять ещё
        else:
            return RES_PROCESSING

    def load_operation(self, op, i=1.0):
        """Загрузить ресурс операцией.
        :param op: операция
        :param i: интенсивность выполнения
        :return status: результат постановки операции на исполнение (RES_REJECTED, RES_PROCESSING)
        """
        if self.Threads < self.MaxThreads and self.Payload < self.MaxIntense:  # пока не забьём все вычислитель и не превысим максимальную производительность
            self.Threads += 1  # задействуем вычислитель
            self.Payload += i  # загружаем ресурс
            self.Fatigue += 1  # запоминаем общий "стаж"
            self.cost += self.price * 1  # рассчитываем стоимость использования ресурса

            return op.execute(1, i)  # передача кодов завершения от операций к решателю
        else:
            return RES_REJECTED

    def Release(self):
        self.Payload = 0
        self.Threads = 0

    def reset(self):
        self.Release()
        self.Fatigue = 0
        self.cost = 0


# DEPRECATED, moved to bpmn_reader.py
def fill_template(dyn, number):
    """Создаёт number реальных процессов по заданному шаблону dyn"""
    real_dyn = GrandSolver('Реальные данные ' + str(number))

    real_dyn.D = dyn.D

    real_dyn.QltList = dyn.QltList.copy()

    # клонирование ресурсов
    protos_res = dict()  # связывает новый созданный ресурс с его прототипом в шаблоне

    for clst in dyn.ClustList.values():
        real_clst = real_dyn.AddClust(clst.Name)
        for res in clst.ResList.values():
            # new_id = uuid1()
            # переписывание ресурсов в новую модель; идентификаторы ресурсов не изменяются
            real_clst.AddRes(res.Name, res.MaxIntense, res.MaxThreads, res.price, res.ID)
            # protos_res[res.ID] = str(new_id)

    # клонирование зон видимости
    real_dyn.res_availability = deepcopy(dyn.res_availability)
    # клонирование зон видимости со смещением
    zone_shift = 0
    for r, z in dyn.res_availability.items():
        real_dyn.res_availability[r] = list(map(lambda x: (x[0] + zone_shift, x[1]), z))
        zone_shift += 12

    # клонирование процессов заданное количество раз
    for sec in range(0, number):

        real_proc = real_dyn.AddProc(u"Proc_" + str(sec + 1), uuid1())
        protos = dict()  # связывает новую созданную операцию с её прототипом в шаблоне

        proc_name = list(dyn.ProcList.values())[0].ID  # получение имени первого процесса (было '1', но не только)
        for op in dyn.get_proc(proc_name).OpList.values():
            # требуется гарантировать уникальность идентификатора операции во всей модели
            new_id = uuid1()
            # new_id =  "op_" + str(randint(1, 100))
            
            real_op = real_proc.add_operation(op.Name, op.A, op.AP,
                                              new_id)  # , op.template_id)
            #real_op = real_proc.add_operation("ИЗД_" + str(sec) + "_" + op.Name, op.A, op.AP,
            #                                  new_id)  # , op.template_id)
            protos[op.ID] = str(new_id)

            # клонирование зон видимости
            if dyn.availability.get(op.ID, False):
                real_dyn.availability[str(new_id)] = dyn.availability[op.ID]
                # Смещение
                # list(map(lambda x: (x[0] + sec * 3, x[1]) if (x[0] + sec * 3 <= dyn.D) else
                # (x[0] + sec * 3 - dyn.D, x[1]),
                #          dyn.availability[op.ID]))
                # real_dyn.availability[str(new_id)].insert(0, (0,0))

            # клонирование штрафных функций
            if dyn.penalty.get(op.ID, False):
                real_dyn.penalty[str(new_id)] = dyn.penalty[op.ID]

                # real_dyn.availability[str(new_id)] = dyn.availability[op.ID]
                # zone_shift = 0
                # for r, z in dyn.res_availability.items():
                #     real_dyn.res_availability[r] = list(map(lambda x: (x[0]+zone_shift, x[1]), z))
                #     zone_shift += 12

            # real_dyn.availability[str(new_id)] = dyn.res_availability[0]

            # матрицу продуктивности дополним новыми связями
            for (clust, res) in dyn.res_iter():
                # if (op.template_id,res.template_id) in dyn.ProductivityMatrix:
                if (op.ID, res.ID) in dyn.ProductivityMatrix:
                    # real_dyn.ProductivityMatrix[(protos[op.ID],protos_res[res.ID])] = dyn.ProductivityMatrix[(op.template_id,res.template_id)]
                    real_dyn.ProductivityMatrix[(real_op.ID, res.ID)] = dyn.ProductivityMatrix[(op.ID, res.ID)]

        # клонирование связей
        real_proc.graph = dyn.get_proc(proc_name).graph.copy()

        # подмена шаблонных идентификаторов узлов на новые
        nx.relabel_nodes(real_proc.graph, protos, copy=False)

    return real_dyn


def clone_model(dyn):
    """Создаёт глубокий клон модели"""
    real_dyn = GrandSolver('Клон модели')

    real_dyn.D = dyn.D

    real_dyn.QltList = deepcopy(dyn.QltList)
    # real_dyn.QltList = {i:list([v[0]]) for i,v in dyn.QltList.items()}

    # клонирование запретов на выполнение
    real_dyn.restriction = deepcopy(dyn.restriction)

    # клонирование зон видимости
    real_dyn.availability = deepcopy(dyn.availability)
    real_dyn.res_availability = deepcopy(dyn.res_availability)

    # клонирование ресурсов
    protos_res = dict()  # связывает новый созданный ресурс с его прототипом в шаблоне

    for clst in dyn.ClustList.values():
        real_clst = real_dyn.AddClust(clst.Name)
        for res in clst.ResList.values():
            # new_id = uuid1()

            real_clst.AddRes(res.Name, res.MaxIntense, res.MaxThreads, res.price, res.ID)
            # protos_res[res.ID] = str(new_id)

    # real_proc = real_dyn.AddProc("Секция", uuid1())
    for proc in dyn.ProcList.values():

        real_proc = real_dyn.AddProc(proc.Name, proc.ID)
        # protos = dict() # связывает новую созданную операцию с её прототипом в шаблоне

        for op in proc.OpList.values():
            # new_id = uuid1()
            real_op = real_proc.add_operation(op.Name, op.A, op.AP, op.ID)
            real_op.X = op.X
            real_op.XP = op.XP

            # protos[op.ID] = str(new_id)

            # матрицу продуктивности дополним новыми связями
            for (clust, res) in dyn.res_iter():
                if (op.ID, res.ID) in dyn.ProductivityMatrix:
                    real_dyn.ProductivityMatrix[(op.ID, res.ID)] = dyn.ProductivityMatrix[(op.ID, res.ID)]

        # клонирование связей
        real_proc.graph = proc.graph.copy()

    # клонирование

    return real_dyn


def read_yaml(file_path):
    try:
        with open(file_path, "r") as f:
            try:
                return yaml.safe_load(f)
            except Exception:
                return
    except Exception:
        return


def get_variable(var_name, default):
    '''Поиск констант в командной строке -> переменных окружения -> конфигурационном файле -> по умолчанию'''
    var_arg = args_dict.get(var_name)
    if var_arg:
        var_arg = type(default)(var_arg)

    var_env = os.environ.get(var_name)
    if var_env:
        if var_env == 'True':
            var_env = True
        elif var_env == 'False':
            var_env = False
        else:
            var_env = type(default)(var_env)
    ya = read_yaml("env.yaml")
    var_file = ya.get(var_name)
    if var_file:
        var_file = type(default)(var_file)

    var = var_arg if var_arg is not None else var_env if var_env is not None else var_file if var_file is not None else default
    color = "blue"
    # var = type(default)(var)
    if isinstance(var, bool):
        color = "green" if var == True else "red"
    click.secho('\t' + var_name.ljust(21, ' ') + '[{4}]\tcmd {0} ->\tenv {1} ->\tyaml {2} ->\tdefault {3}'.format(
        var_arg, var_env, var_file, default, var), fg=color, bold=True)
    return var


@click.command()
@click.argument('file', type=str, required=True)  # default=sys.stdin для потокового ввода
@click.argument('args', nargs=-1)
def main(file, args):
    if not file:
        file = 'models/pavlov/test1.xml'
        file = 'test.xml'
        file = 'tests/basic.xml'
        file = 'tests/basic2.xml'  # ЗАЦИКЛИВАНИЕ
        file = 'models/common/robo.bpmn'  # Чтение BPMN
        file = 'models/common/satellite.bpmn'  # Чтение BPMN
        file = 'models/monsg.bpmn'  # Чтение BPMN
        file = 'models/monsg-FINAL_gateway.bpmn'  # Чтение BPMN
        file = 'models/monsg-FINAL_gateway-ispr-final.bpmn'  # Чтение BPMN
        file = 'models/monsg-FINAL_gateway-ispr-final (2).bpmn'  # Чтение BPMN
        file = 'models/monsg-FINAL_gateway-ispr-final (2)-simple.bpmn'  # Чтение BPMN
        file = 'models/silos_uborka_simple.bpmn'  # Чтение BPMN
        # file = 'monsg-FINAL_gateway-ispr-final(3).bpmn'
        file = 'models/pavlov/mytry.bpmn'
    global args_dict
    args_dict = dict(zip(args[::2], args[1::2]))
    # print(args_dict)
    click.secho('Определение констант: ', fg="yellow", bold=True)

    global DEBUG
    DEBUG = get_variable('DEBUG', True)
    global DEBUG_L1
    DEBUG_L1 = get_variable('DEBUG_L1', False)
    global DEBUG_L2
    DEBUG_L2 = get_variable('DEBUG_L2', False)
    global DEBUG_Q
    DEBUG_Q = get_variable('DEBUG_Q', True)
    global DEBUG_FRONT
    DEBUG_FRONT = get_variable('DEBUG_FRONT', False)
    global DEBUG_PULP
    DEBUG_PULP = get_variable('DEBUG_PULP', False)
    global DEBUG_INTERRUPT
    DEBUG_INTERRUPT = get_variable('DEBUG_INTERRUPT', False)
    global DEBUG_EXEC
    DEBUG_EXEC = get_variable('DEBUG_EXEC', False)
    global DEBUG_NORMALIZE
    DEBUG_NORMALIZE = get_variable('DEBUG_NORMALIZE', False)
    global DEBUG_GRAPH
    DEBUG_GRAPH = get_variable('DEBUG_GRAPH', False)
    global DEBUG_TRANS
    DEBUG_TRANS = get_variable('DEBUG_TRANS', True)
    global DEBUG_REV
    DEBUG_REV = get_variable('DEBUG_REV', False)
    global PRINT
    PRINT = get_variable('PRINT', False)
    global DEBUG_CTRL
    DEBUG_CTRL = get_variable('DEBUG_CTRL', True)

    global WRITE_FILE
    WRITE_FILE = get_variable('WRITE_FILE', False)

    global SIMPLE_DECISION
    SIMPLE_DECISION = get_variable('SIMPLE_DECISION', False)

    global NORMALIZE_LOG_OP
    NORMALIZE_LOG_OP = get_variable('NORMALIZE_LOG_OP', False)
    global NORMALIZE_LOG_ST
    NORMALIZE_LOG_ST = get_variable('NORMALIZE_LOG_ST', False)
    global NORMALIZE_LOG_ANGLE
    NORMALIZE_LOG_ANGLE = get_variable('NORMALIZE_LOG_ANGLE', True)

    global FILE_RESULT_GANT
    FILE_RESULT_GANT = get_variable('FILE_RESULT_GANT', True)
    global FILE_RESULT_LIST
    FILE_RESULT_LIST = get_variable('FILE_RESULT_LIST', False)
    global FILE_RESULT_CHART
    FILE_RESULT_CHART = get_variable('FILE_RESULT_CHART', False)

    global HAMILTONIAN_THINNING
    HAMILTONIAN_THINNING = get_variable('HAMILTONIAN_THINNING', 2)

    global PLOT_GANT
    PLOT_GANT = get_variable('PLOT_GANT', True)

    click.secho('Модель планирования: ' + str(file), fg="yellow", bold=True)

    Dyn = GrandSolver('Шаблон')
    print("Чтение начал")
    # читаем модель всеми известными способами
    if file.lower().endswith('.xml'):
        dyn = Dyn.read_xml(file)
        real_dyn = fill_template(dyn, dyn.Threads or 1)  # Количество клонов модели (параллельных процессов!)
    elif file.lower().endswith('.bpmn'):
        print('чтение bpmn') #делает
        dyn = Dyn.read_bpmn(file)
        print(dyn) # сюда не доходит
        real_dyn = fill_template(dyn, dyn.Threads or 1)  # Количество клонов модели (параллельных процессов!)
        print("чтение bpmn завершено")
        pass
    print("Чтение завершено")
    # real_dyn = dyn

    if DEBUG:
        print("Количество процессов", len(real_dyn.ProcList))

    # PAVLOV: здесь менять допуск на разрывность операций (relaxed=True - с разрывами)
    real_dyn.calculate_plan(dict(method="PULP", relaxed=False))

    if DEBUG:
        print("Интервал планирования: %s" % real_dyn.D)
        print("=" * 60)
        print('Построение расписания')

    best_iteration = real_dyn.DetectAnyTime()
    real_dyn.BuildSchedule(best_iteration)

    if DEBUG_Q:
        print("Лучшая итерация:", best_iteration)
        for q, v in real_dyn.QltList.items():
            # if v[0] > 0:
            print(q, end=": ")
            for qx in v:
                print(qx, end=" ")
            print()

        for (proc, op) in sorted(real_dyn.Schedule,
                                 key=lambda proc_op: real_dyn.Schedule[(proc_op[0], proc_op[1])][0]['start'] if len(
                                     real_dyn.Schedule[(proc_op[0], proc_op[1])]) > 0 else -1):
            if len(real_dyn.Schedule[(proc, op)]):
                print(proc.Name, op.Name + " (" + str(real_dyn.OpPriorMatrix.get(op.ID, None)) + ")")
                for i in real_dyn.Schedule[(proc, op)]:
                    print("\t" + str(i['start']) + " -- " + str(i.get('stop')) + " : " + i.get('res', {
                        'Name': '--'}).Name + " @ " + str(i['intens']))


    #print(json.dumps((real_dyn.QltList)))
    #main.init(real_dyn.QltList)
    #settings.d.update(real_dyn.QltList)
    """obj = []
    for i, val in real_dyn.QltList:
        obj.append({i, val})
    print(obj)"""
    #d = real_dyn.QltList
    #print(d)

    #return real_dyn.QltList
    if FILE_RESULT_GANT:
        print('Запись диаграммы Ганта')
        real_dyn.SaveGanttXML("result.xml")

    if FILE_RESULT_LIST:
        print('Запись таблицы показателей')
        real_dyn.SaveListXML("list.xml")

    if FILE_RESULT_CHART:
        print('Запись диаграммы ресурсов')
        real_dyn.SaveChartXML("chart.xml")
    import json
    outputJson = {
        'QltList': real_dyn.QltList,
        'WorkTask': [],
        'WorkResource': [],
        'ALL_OUTPUT': []
    }
    print(outputJson)
    '''
    with open('temp.json', 'w') as fp:
        json.dump(real_dyn.QltList, fp)
        #print(real_dyn.SaveChartXML())'''
    if PLOT_GANT:

        # import plotly
        import plotly.figure_factory as ff
        import plotly.express as px
        from datetime import datetime, timedelta
        import random
        from pandas import DataFrame

        import warnings
        warnings.filterwarnings('ignore', category=FutureWarning)

        # Отрисовка показателей качества
        import json
        # from pprint import pprint
        # pprint(real_dyn.QltList)
        qlt = deepcopy(real_dyn.QltList)
        for k, v in list(qlt.items())[1:]:
            # забиваем нулями то, что не соответствует длине
            # print(qlt)
            if len(v) != len(qlt['J0']):
                qlt[k] = [0 for _ in range(len(qlt['J0']))]
            # избавляемся от нулевых показателей
            if max(qlt[k][1:]) == 0:
                del qlt[k]
                continue
            # qlt[k] = qlt[k][1:]                     # избавляемся от приоритета показателя
            max_i = max(qlt[k])
            if max_i > 0:
                qlt[k] = [v[0]] + [i / max_i for i in v[1:]]  # нормализуем показатели

            # избавляемся от незначимых показателей
            # if not v[0]:
            #    del qlt[k]

        # print()

        del qlt['J0']
        # pprint(qlt)
        # qlt = json.dumps(qlt)

        # таблица показателей
        from itertools import zip_longest

        head = '''
    <!-- JQuery -->
    <script src="gantt/js/jquery-3.5.1.js"></script>
    <!-- Popper.js first, then Bootstrap JS -->
    <script src="gantt/js/popper.min.js"></script>
    <!-- Bootstrap 5 -->
    <link href="gantt/css/bootstrap.min.css" rel="stylesheet">
    <script src="gantt/js/bootstrap.bundle.min.js"></script>
    <!-- Bootstrap 5 icons -->
    <link rel="stylesheet" href="gantt/css/bootstrap-icons.css">

    <!-- DataTables -->
    <script src="gantt/js/jquery.dataTables.min.js"</script>
    <script src="gantt/js/dataTables.bootstrap5.min.js"</script>
    <link rel="stylesheet" type="text/css" href="gantt/css/bootstrap.min.css">
    <link rel="stylesheet" type="text/css" href="gantt/css/dataTables.bootstrap5.min.css">
            '''

        head += '''<script type="text/javascript" class="init">$(document).ready(function () {
        var table = $('#example').DataTable({
        language: {

                        "processing": "Подождите...",
                        "search": "Поиск:",
                        "lengthMenu": "Показать _MENU_ записей",
                        "info": "Записи с _START_ до _END_ из _TOTAL_ записей",
                        "infoEmpty": "Записи с 0 до 0 из 0 записей",
                        "infoFiltered": "(отфильтровано из _MAX_ записей)",
                        "infoPostFix": "",
                        "loadingRecords": "Загрузка записей...",
                        "zeroRecords": "Записи отсутствуют.",
                        "emptyTable": "В таблице отсутствуют данные",
                        "paginate": {
                            "first": "Первая",
                            "previous": "Предыдущая",
                            "next": "Следующая",
                            "last": "Последняя"
                        },
                        "aria": {
                            "sortAscending": ": активировать для сортировки столбца по возрастанию",
                            "sortDescending": ": активировать для сортировки столбца по убыванию"
                        },
                        "select": {
                            "rows": {
                                "_": "Выбрано записей: %d",
                                "0": "Кликните по записи для выбора",
                                "1": "Выбрана одна запись"
                            }
                        }

        },
    });

    $('#example tbody').on('click', 'tr', function () {
        var data = table.row( this ).data();
        alert( 'You clicked on '+data[0]+' row' );
    } );

    });
    </script>'''

        table = '<table id="example" class="table table-striped table-bordered table-hover" cellspacing="0" width="100%">'
        thead = '<thead><tr>'
        thead += '<th>' + 't' + '</th>'
        for j in real_dyn.QltList.keys():
            thead += '<th>' + j + '</th>'
        thead += '</tr></thead>'
        table += thead + '<tbody>'

        for i, lst in enumerate(zip_longest(*real_dyn.QltList.values(), fillvalue=0.0)):
            if not i:
                continue  # игнорирование первого списка значений (коэффициенты важности показателей)
            table += '<tr>'
            table += '<td>' + str(i) + '</td>'  # номер итерации
            for j in lst:
                table += '<td>' + str(j) + '</td>'
            table += '</tr>'

        table += '</tbody>'
        table += thead.replace('thead', 'tfoot')
        table += '</table>'

        # лепестковая диаграмма
        import plotly.graph_objects as go

        categories = [k + ' priority=' + str(v[0]) for k, v in list(qlt.items())]
        categories = [*categories, categories[0]]

        fig = go.Figure()
        for i in range(1, len(list(qlt.values())[0])):
            r = [v[i] for k, v in list(qlt.items())]
            fig.add_trace(go.Scatterpolar(
                r=[*r, r[0]],
                theta=categories,
                fill='toself',
                name='i=' + str(i)
            ))

        fig.update_layout(
            polar=dict(
                radialaxis=dict(
                    visible=True,
                    range=[0, 1]
                )),
            showlegend=True
        )

        # fig.show()

        # офлайн визуализация всего в один html-файл
        with open('p_graph.html', 'w', encoding="utf-8") as f:
            f.write('<html>')
            f.write(head)
            f.write('<body>')

            f.write('<div class="container-fluid">')
            f.write('  <div class="row">')
            f.write('    <div class="col-sm-4">')
            f.write(fig.to_html(full_html=False, include_plotlyjs=True))  # первый True, остальные False
            f.write('    </div>')
            f.write('    <div class="col-sm-8">')
            f.write(table)
            f.write('    </div>')
            f.write('  </div>')

            f.write('<nav>')
            f.write('  <div class="nav nav-tabs" id="nav-tab" role="tablist">')
            for it, lst in enumerate(zip_longest(*real_dyn.QltList.values(), fillvalue=0.0)):
                if not it or it == 0:
                    continue
                is_or_not_active = 'active' if it == best_iteration else ''
                aria_selected = 'true' if it == best_iteration else 'false'
                f.write('    <button class="nav-link ' + is_or_not_active + '" id="nav-' + str(
                    it) + '-tab" data-bs-toggle="tab" data-bs-target="#nav-' + str(
                    it) + '" type="button" role="tab" aria-controls="nav-' + str(
                    it) + '" aria-selected="' + aria_selected + '">' + str(it) + '</button>')
            f.write('  </div>')
            f.write('</nav>')

            f.write('<div class="tab-content" id="nav-tabContent">')

            for it, lst in enumerate(zip_longest(*real_dyn.QltList.values(), fillvalue=0.0)):
                if not it or it == 0:
                    continue
                if it != best_iteration:  # временно выводим только лучшую итерацию
                    pass  # continue
                real_dyn.BuildSchedule(it)  # it = iteration
                # Отрисовка графиков
                # now = datetime.today().strftime('%Y-%m-%d %H:%M:')
                now = datetime.min

                # now = datetime.today()
                # ГРАФИК ПО ОПЕРАЦИЯМ - ВЫДЕЛЕНИЕ ЦВЕТОВ ПО РЕСУРСУ
                df = []
                annots = []  # аннотации к графикам
                for ProcOp, IntResStartStop in real_dyn.Schedule.items():
                    proc, oper = ProcOp
                    task = str(oper.Name)
                    # убираем пустые операции из расписания (added by Palich)
                    if not IntResStartStop:
                        continue
                    start = (now + timedelta(0, IntResStartStop[0]['start'])).strftime('%Y-%m-%d %H:%M:%S')
                    finish = (now + timedelta(0, IntResStartStop[0]['stop'])).strftime('%Y-%m-%d %H:%M:%S')
                    resource = str(IntResStartStop[0]['res'].Name)
                    # intens = IntResStartStop[0]['intens']
                    opprior = '%.2E' % real_dyn.OpPriorMatrix[ProcOp[1].ID]
                    # ПОНЯТЬ ОТКУДА БЕРУТСЯ ПРИОРИТЕТЫ
                    opprior = '%.2E' % real_dyn.Priorities_all[ProcOp[1].ID] if ProcOp[
                                                                                    1].ID in real_dyn.Priorities_all else 0
                    # print(dict(Task=task, Start=now+start, Finish=now+finish, Resource=resource))
                    # df.append(dict(Task=task, Start=start, Finish=finish, Resource=resource, Intens = intens))
                
                    df.append(dict(Task=task, Start=start, Finish=finish, Resource=resource, Opprior=opprior))
                    

                df.sort(key=lambda x: x["Task"], reverse=True)
                
                
                
                ######
                r = lambda: random.randint(0, 255)
                col = (r(), r(), r())
                r_col = (255 - col[0], 255 - col[1], 255 - col[2])
                colors = ['#%02X%02X%02X' % col]  # цвета ресурсов
                r_colors = ['#%02X%02X%02X' % r_col]  # реверсивные цвета для текста на столбцах
                set_res = list(set([i['Resource'] for i in df]))
                for i in range(1, len(set_res) + 1):
                    col = (r(), r(), r())
                    r_col = (255 - col[0], 255 - col[1], 255 - col[2])
                    colors.append('#%02X%02X%02X' % col)
                    r_colors.append('#%02X%02X%02X' % r_col)
                #####
                title1 = 'Расписание работ по операциям'
                fig1 = ff.create_gantt(df, title=title1, colors=colors, index_col='Resource', show_colorbar=True,
                                       group_tasks=False, showgrid_x=True, showgrid_y=True)
                fig1.update_layout(overwrite=True, legend_traceorder="grouped")
                #  визуализация  при явном указании диапазона времени
                max_x = max([i['Finish'] for i in df])
                min_x = min([i['Start'] for i in df])
                fig1.update_layout(xaxis_range=[min_x, max_x])
                fig1.update_layout(legend=dict(yanchor="top", y=0.9, xanchor="left", x=0.9))

                # Текстовая аннтотация к столбикам
                from dateutil.parser import parse
                for i in range(len(df)):
                    # Вычисляем куда шлепать надпись
                    a = parse(df[i]['Start'])
                    b = parse(df[i]['Finish'])
                    LabelDate = a + (b - a) / 2
                    # text = df[i]['Task']
                    text = df[i]['Opprior']
                    annots.append(dict(x=LabelDate, y=i, text=text, showarrow=False,
                                       font=dict(color=r_colors[set_res.index(df[i]['Resource'])])))

                # plot figure
                fig1['layout']['annotations'] = annots

                grafparam = {
                    'id': it,
                    'data': df,
                    'colors': colors,
                }
                outputJson["WorkTask"].append(grafparam)

                # ГРАФИК ПО РЕСУРСАМ - ВЫДЕЛЕНИЕ ЦВЕТОВ ПО ОПЕРАЦИИ
                df = []
                print(real_dyn.Schedule.items())
                dataALL = {
                        'id': it,
                        'data': [],
                    }
                for ProcOp, IntResStartStop in real_dyn.Schedule.items():
                    #print(IntResStartStop)
                    
                    proc, oper = ProcOp
                    #print(oper.Name, oper.A, oper.AP, oper.X, oper.XP)
                    #print(proc.Name, proc.OpList, proc.ID)
                    task = str(oper.Name)
                    # убираем пустые операции из расписания (added by Palich)
                    if not IntResStartStop:
                        continue
                    start = (now + timedelta(0, IntResStartStop[0]['start'])).strftime('%Y-%m-%d %H:%M:%S').zfill(19)
                    #print(datetime.now())
                    #print(IntResStartStop[0]['res'])
                    #print((datetime.now() + timedelta(0, IntResStartStop[0]['start'])).strftime('%Y-%m-%d %H:%M:%S').zfill(19))
                    finish = (now + timedelta(0, IntResStartStop[0]['stop'])).strftime('%Y-%m-%d %H:%M:%S').zfill(19)
                    resource = str(IntResStartStop[0]['res'].Name)
                    # print(dict(Task=task, Start=now+start, Finish=now+finish, Resource=resource))
                    dataOutput = {
                        'oper_Name': str(oper.Name),
                        'oper_A': str(oper.A),
                        'oper_AP': str(oper.AP),
                        'oper_X': str(oper.X),
                        'oper_XP': str(oper.XP),
                        'res': {
                            'start': IntResStartStop[0]['start'],
                            'stop': IntResStartStop[0]['stop'],
                            'intens': IntResStartStop[0]['intens'],
                            'Name': IntResStartStop[0]['res'].Name,
                        } 
                    }
                    dataALL["data"].append(dataOutput)
                    df.append(dict(Task=resource, Start=start, Finish=finish, Resource=task))

                df.sort(key=lambda x: x["Task"], reverse=False)
                
                outputJson['ALL_OUTPUT'].append(dataALL)
                ######
                r = lambda: random.randint(0, 255)
                colors = ['#%02X%02X%02X' % (r(), r(), r())]
                for i in range(1, len(set([i['Resource'] for i in df])) + 1):
                    colors.append('#%02X%02X%02X' % (r(), r(), r()))
                #####
                title2 = 'Расписание работ по ресурсам'
                fig2 = ff.create_gantt(df, title=title2, colors=colors, index_col='Resource', show_colorbar=True,
                                       group_tasks=True, showgrid_x=True, showgrid_y=True)
                fig2.update_layout(overwrite=True, legend_traceorder="grouped")
                #  визуализация  при явном указании диапазона времени
                max_x2 = max([i['Finish'] for i in df])
                min_x2 = min([i['Start'] for i in df])
                fig2.update_layout(xaxis_range=[min_x2, max_x2])
                fig2.update_layout(legend=dict(yanchor="top", y=0.9, xanchor="left", x=0.9))
                grafparam = {
                    'id': it,
                    'data': df,
                    'colors': colors
                }
                outputJson["WorkResource"].append(grafparam)



                is_or_not_active = 'show active' if it == best_iteration else ''
                aria_selected = 'true' if it == best_iteration else 'false'
                f.write('<div class="tab-pane fade ' + is_or_not_active + '" id="nav-' + str(
                    it) + '" role="tabpanel" aria-labelledby="nav-' + str(it) + '-tab" tabindex="0">')

                f.write('  <div class="row">')
                f.write('    <div class="col-sm">')
                f.write(fig1.to_html(full_html=False, include_plotlyjs=False))
                f.write('    </div>')
                f.write('  </div>')
                f.write('  <div class="row">')
                f.write('    <div class="col-sm">')
                f.write(fig2.to_html(full_html=False, include_plotlyjs=False))
                f.write('    </div>')
                f.write('  </div>')
                # f.write('</div>')

                f.write('</div>')

            # f.write('</div>')
            f.write('</div>')

            f.write('</body>')
            f.write('</html>')
            print(outputJson)
            with open('temp.json', 'w') as fp:
                json.dump(outputJson, fp)
        # import os
        # os.system("start p_graph.html")

if __name__ == '__main__':
    ya = read_yaml("env.yaml")
    main()