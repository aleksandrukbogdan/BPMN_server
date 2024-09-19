if PLOT_GANT:
        '''
        import plotly.figure_factory as ff

        df = [dict(Task="Job-1", Start='2017-01-01', Finish='2017-02-02', Resource='Complete'),
            dict(Task="Job-1", Start='2017-02-15', Finish='2017-03-15', Resource='Incomplete'),
            dict(Task="Job-2", Start='2017-01-17', Finish='2017-02-17', Resource='Not Started'),
            dict(Task="Job-2", Start='2017-01-17', Finish='2017-02-17', Resource='Complete'),
            dict(Task="Job-3", Start='2017-03-10', Finish='2017-03-20', Resource='Not Started'),
            dict(Task="Job-3", Start='2017-04-01', Finish='2017-04-20', Resource='Not Started'),
            dict(Task="Job-3", Start='2017-05-18', Finish='2017-06-18', Resource='Not Started'),
            dict(Task="Job-4", Start='2017-01-14', Finish='2017-03-14', Resource='Complete')]

        colors = {'Not Started': 'rgb(220, 0, 0)',
                'Incomplete': (1, 0.9, 0.16),
                'Complete': 'rgb(0, 255, 100)'}

        fig = ff.create_gantt(df, colors=colors, index_col='Resource', show_colorbar=True,
                            group_tasks=True)
        fig.show()

        #from pprint import pprint
        #pprint(real_dyn.Schedule)
        '''

        #import plotly
        import plotly.figure_factory as ff
        import plotly.express as px
        from datetime import datetime, timedelta
        import random
        #from pandas import DataFrame

        import warnings
        warnings.filterwarnings('ignore', category=FutureWarning)

        # Отрисовка показателей качества
        #import json
        #from pprint import pprint
        #pprint(real_dyn.QltList)
        qlt = deepcopy(real_dyn.QltList)
        for k,v in list(qlt.items()):
            # забиваем нулями то, что не соответствует длине
            if len(v) != len(qlt['J0']):
                qlt[k] = [0 for _ in range(len(qlt['J0']))]
            # избавляемся от нулевых показателей
            if max(qlt[k][1:]) == 0:
                del qlt[k]
                continue
            #qlt[k] = qlt[k][1:]                     # избавляемся от приоритета показателя
            max_i = max(qlt[k])
            if max_i > 0:
                qlt[k] = [v[0]] + [i/max_i for i in v[1:]]    # нормализуем показатели
            

            # избавляемся от незначимых показателей
            #if not v[0]:
            #    del qlt[k]

        #print()

        del qlt['J0']
        #pprint(qlt)
        #qlt = json.dumps(qlt)

        # таблица показателей
        from itertools import zip_longest

        head = '''
<meta name="viewport" content="width=device-width, initial-scale=1">
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
        thead += '<th>' + 't' +'</th>'
        for j in real_dyn.QltList.keys():
            thead += '<th>' + j +'</th>'
        thead += '</tr></thead>'
        table += thead + '<tbody>'

        for i,lst in enumerate(zip_longest(*real_dyn.QltList.values(), fillvalue=0.0)):
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

        categories = [k + ' priority=' + str(v[0]) for k,v in list(qlt.items())]
        categories = [*categories, categories[0]]

        fig = go.Figure()
        for i in range(1, len(list(qlt.values())[0])):
            r = [v[i] for k,v in list(qlt.items())]
            fig.add_trace(go.Scatterpolar(
                r=[*r, r[0]],
                theta=categories,
                fill='toself',
                name='i='+ str(i)
            ))

        fig.update_layout(
        polar=dict(
            radialaxis=dict(
            visible=True,
            range=[0, 1]
            )),
        showlegend=True
        )

        #fig.show()
        



        # офлайн визуализация всего в один html-файл
        with open('p_graph.html', 'w', encoding="utf-8") as f:
            f.write('<!DOCTYPE html><html lang="ru">')
            f.write(head)
            f.write('<body>')

            f.write('<div class="container-fluid">')
            f.write('  <div class="row">')
            f.write('    <div class="col-sm-4">')
            f.write(fig.to_html(full_html=False, include_plotlyjs=True))    # первый True, остальные False
            f.write('    </div>')
            f.write('    <div class="col-sm-8">')
            f.write(table)
            f.write('    </div>')
            f.write('  </div>')


            f.write('<nav>')
            f.write('  <div class="nav nav-tabs" id="nav-tab" role="tablist">')
            for it,lst in enumerate(zip_longest(*real_dyn.QltList.values(), fillvalue=0.0)):
                if not it or it == 0:
                    continue
                is_or_not_active = 'active' if it == best_iteration else ''
                aria_selected = 'true' if it == best_iteration else 'false'
                f.write('    <button class="nav-link ' + is_or_not_active + '" id="nav-' + str(it) + '-tab" data-bs-toggle="tab" data-bs-target="#nav-' + str(it) + '" type="button" role="tab" aria-controls="nav-' + str(it) + '" aria-selected="' + aria_selected + '">' + str(it) + '</button>')
            f.write('  </div>')
            f.write('</nav>')

            f.write('<div class="tab-content" id="nav-tabContent">')

            for it,lst in enumerate(zip_longest(*real_dyn.QltList.values(), fillvalue=0.0)):
                if not it or it == 0:
                    continue
                if it != best_iteration: # временно выводим только лучшую итерацию
                    pass #continue
                real_dyn.BuildSchedule(it)   # it = iteration

                # Отрисовка графиков
                #now = datetime.today().strftime('%Y-%m-%d %H:%M:') 
                now = datetime.min
                #now = datetime.today()
                # ГРАФИК ПО ОПЕРАЦИЯМ - ВЫДЕЛЕНИЕ ЦВЕТОВ ПО РЕСУРСУ
                df = []
                annots = [] # аннотации к графикам
                for ProcOp, IntResStartStop in real_dyn.Schedule.items():
                    proc, oper = ProcOp
                    task = str(oper.Name)
                    # убираем пустые операции из расписания (added by Palich)
                    if not IntResStartStop:
                        continue
                    start = (now + timedelta(0, IntResStartStop[0]['start'])).strftime('%Y-%m-%d %H:%M:%S')
                    finish = (now + timedelta(0, IntResStartStop[0]['stop'])).strftime('%Y-%m-%d %H:%M:%S')
                    resource = str(IntResStartStop[0]['res'].Name)
                    #intens = IntResStartStop[0]['intens']
                    opprior = '%.2E' % real_dyn.OpPriorMatrix[ProcOp[1].ID]
                    # ПОНЯТЬ ОТКУДА БЕРУТСЯ ПРИОРИТЕТЫ
                    opprior = '%.2E' % real_dyn.Priorities_all[ProcOp[1].ID] if ProcOp[1].ID in real_dyn.Priorities_all else 0
                    #print(dict(Task=task, Start=now+start, Finish=now+finish, Resource=resource))
                    #df.append(dict(Task=task, Start=start, Finish=finish, Resource=resource, Intens = intens))
                    df.append(dict(Task=task, Start=start, Finish=finish, Resource=resource, Opprior = opprior))

                df.sort(key=lambda x: x["Task"], reverse=True)
                # если расписание пустое, то его не показываем
                if not df: continue

                ######
                r = lambda: random.randint(0,255)
                col = (r(),r(),r())
                r_col = (255 - col[0], 255 - col[1], 255 - col[2])
                colors = ['#%02X%02X%02X' % col]        # цвета ресурсов
                r_colors = ['#%02X%02X%02X' % r_col]    # реверсивные цвета для текста на столбцах
                set_res = list(set([i['Resource'] for i in df]))
                for i in range(1, len(set_res) + 1):
                    col = (r(),r(),r())
                    r_col = (255 - col[0], 255 - col[1], 255 - col[2])
                    colors.append('#%02X%02X%02X' % col)
                    r_colors.append('#%02X%02X%02X' % r_col)
                #####
                title1 = 'Расписание работ по операциям'
                fig1 = ff.create_gantt(df, title=title1, colors=colors, index_col='Resource', show_colorbar=True,
                                    group_tasks=False, showgrid_x=True, showgrid_y=True)
                fig1.update_layout(legend_traceorder="grouped")
                #  визуализация  при явном указании диапазона времени
                max_x = max([i['Finish']for i in df])
                min_x = min([i['Start']for i in df])
                fig1.update_layout(xaxis_range=[min_x, max_x])
                fig1.update_layout(legend=dict(yanchor="top", y=0.9, xanchor="left", x=0.9))
                
                fig1.update_traces(marker_line_color='yellow', marker_line_width=1, opacity=0.6)
                fig1.update_traces(mode='lines', line_color='yellow', selector=dict(fill='toself'))

                # Текстовая аннтотация к столбикам
                from dateutil.parser import parse
                for i in range(len(df)):
                    # Вычисляем куда шлепать надпись
                    a = parse(df[i]['Start'])
                    b = parse(df[i]['Finish'])
                    LabelDate = a + (b - a)/2
                    #text = df[i]['Task']
                    text = df[i]['Opprior']
                    annots.append(dict(x=LabelDate,y=i,text=text, showarrow=False, font=dict(color=r_colors[set_res.index(df[i]['Resource'])])))

                # plot figure
                fig1['layout']['annotations'] = annots


                # ГРАФИК ПО РЕСУРСАМ - ВЫДЕЛЕНИЕ ЦВЕТОВ ПО ОПЕРАЦИИ
                df = []
                for ProcOp, IntResStartStop in real_dyn.Schedule.items():
                    proc, oper = ProcOp
                    task = str(oper.Name)
                    # убираем пустые операции из расписания (added by Palich)
                    if not IntResStartStop:
                        continue
                    start = (now + timedelta(0, IntResStartStop[0]['start'])).strftime('%Y-%m-%d %H:%M:%S')
                    finish = (now + timedelta(0, IntResStartStop[0]['stop'])).strftime('%Y-%m-%d %H:%M:%S')
                    resource = str(IntResStartStop[0]['res'].Name)
                    #print(dict(Task=task, Start=now+start, Finish=now+finish, Resource=resource))
                    df.append(dict(Task=resource, Start=start, Finish=finish, Resource=task))

                df.sort(key=lambda x: x["Task"], reverse=False)

                ######
                r = lambda: random.randint(0,255)
                colors = ['#%02X%02X%02X' % (r(),r(),r())]
                for i in range(1, len(set([i['Resource'] for i in df])) + 1):
                    colors.append('#%02X%02X%02X' % (r(),r(),r()))
                #####
                title2 = 'Расписание работ по ресурсам'
                fig2 = ff.create_gantt(df, title=title2, colors=colors, index_col='Resource', show_colorbar=True,
                                    group_tasks=True, showgrid_x=True, showgrid_y=True)
                fig2.update_layout(overwrite=True, legend_traceorder="grouped")
                #  визуализация  при явном указании диапазона времени
                max_x2 = max([i['Finish']for i in df])
                min_x2 = min([i['Start']for i in df])
                fig2.update_layout(xaxis_range=[min_x2, max_x2])
                fig2.update_layout(legend=dict(yanchor="top", y=0.9, xanchor="left", x=0.9))
                
                fig2.update_traces(marker_line_color='yellow', marker_line_width=1, opacity=0.6)
                fig2.update_traces(mode='lines', line_color='yellow', selector=dict(fill='toself'))


                '''from plotly.subplots import make_subplots
                fig12 = make_subplots(rows=2, cols=1, shared_xaxes=True)
                fig12.append_trace(fig1._data_objs, row=1, col=1)
                fig12.append_trace(fig2._data_objs, row=2, col=1)
                fig12.update_layout(height=600, width=600, title_text="Stacked Subplots")
                fig12.show()'''

                #fig1.show() #Стандартный показ в браузере (требуется интернет) - нестабильный вариант

                ## офлайн визуализация в браузере - стабильнывй вариант
                ## требуется gantt.html + папака js
                #import json
                #graphJSON1 = json.dumps(fig1, cls=plotly.utils.PlotlyJSONEncoder)
                #with open('gantt/gantt_1.JSON', 'w') as file:
                #    file.write('var graphs = {};'.format(graphJSON1))

                #graphJSON2 = json.dumps(fig1, cls=plotly.utils.PlotlyJSONEncoder)
                #with open('gantt/gantt_2.JSON', 'w') as file:
                #    file.write('var graphs = {};'.format(graphJSON2))

                is_or_not_active = 'show active' if it == best_iteration else ''
                aria_selected = 'true' if it == best_iteration else 'false'
                f.write('<div class="tab-pane fade ' + is_or_not_active + '" id="nav-' + str(it) + '" role="tabpanel" aria-labelledby="nav-' + str(it) + '-tab" tabindex="0">')



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
                #f.write('</div>')


                f.write('</div>')

            #f.write('</div>')
            f.write('</div>')
                
            f.write('</body>')
            f.write('</html>')
        
        #import os
        #os.system("start p_graph.html")

