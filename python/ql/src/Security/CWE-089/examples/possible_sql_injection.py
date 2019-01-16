
from django.conf.urls import patterns, url

urlpatterns = patterns(url(r'^save_name/$',
                           upload, name='save_name'))


def make_query(request):
    if request.method == 'POST':
        name = request.POST.get('name')
        return "insert into names_file ('name') values ('%s')" % name
