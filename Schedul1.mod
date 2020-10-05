/*********************************************
 * OPL 12.9.0.0 Model
 * Author: Ася Троян
 * Creation Date: Sep 28, 2020 at 1:36:46 PM
 *********************************************/
{string} rooms = ...;
{string} teachers = ...;
{string} classes = ...;
{int} lessons = ...;

int roomTeachersRelation [rooms][teachers]= ...;
int teacherClassRelation [teachers][classes] = ...;
int classLessonRelation [classes][lessons] = ...;
int teacherLessonRelation [teachers][lessons] = ...;

dvar int schedule [rooms][teachers][classes][lessons] in 0..1;

maximize 
sum(r in rooms, t in teachers, c in classes, l in lessons)
   schedule[r][t][c][l] * roomTeachersRelation[r][t];

 subject to
{
 forall(
 	r in rooms, 
 	t in teachers : roomTeachersRelation[r][t] == 0, 
 	c in classes : teacherClassRelation[t][c] == 0, 
 	l in lessons : classLessonRelation[c][l] == 0 && teacherLessonRelation[t][l] == 0
 	)
   schedule[r][t][c][l] == 0;
   
  forall( t in teachers, c in classes) 
  sum(r in rooms, l in lessons)
     schedule[r][t][c][l] == teacherClassRelation[t][c];
     
  forall( t in teachers, l in lessons)   
  	sum(r in rooms, c in classes) 
  		schedule[r][t][c][l] == 1;
}  
