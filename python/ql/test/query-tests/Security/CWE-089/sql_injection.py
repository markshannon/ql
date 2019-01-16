
from django.conf.urls import patterns, url
from django.db import connection, models
from django.db.models.expressions import RawSQL

class Name(models.Model):
    pass

def save_name(request):
    query_template = load_template()

    if request.method == 'POST':
        name = request.POST.get('name')
        curs = connection.cursor()
        #GOOD -- Using parameters
        curs.execute(query_template, name)
        #BAD -- Using string formatting
        curs.execute(query_template % name)

        #BAD -- other ways of executing raw SQL code with string interpolation
        Name.objects.annotate(RawSQL(query_template % name))
        Name.objects.raw(query_template + name)
        Name.objects.extra(query_template % name)

urlpatterns = patterns(url(r'^save_name/$',
                           save_name, name='save_name'))

def construct_query(request):

    if request.method == 'POST':
        name = request.POST.get('name')
        return "INSERT INTO names_file ('name') VALUES ('%s')" % name

urlpatterns = patterns(url(r'^save_name/$', save_name, name='save_name'),
                       url(r'^other/$', construct_query, name='other'),
                       )
