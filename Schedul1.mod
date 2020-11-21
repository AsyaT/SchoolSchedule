/*********************************************
 * OPL 12.9.0.0 Model
 * Author: Ася Троян
 * Creation Date: Sep 28, 2020 at 1:36:46 PM
 *********************************************/
{string} rooms = ...;
{string} teachers = ...;
{string} foreignLangTeachers = ...;
{string} trudyTeachers = ...;
{string} classes = ...;
{int} lessons = ...;

int roomTeachersRelation [rooms][teachers]= ...;
int teacherClassRelation [teachers][classes] = ...;
int classLessonRelation [classes][lessons] = ...;
int teacherLessonRelation [teachers][lessons] = ...;

dvar int TeacherLessonResult[teachers][lessons] ;
dvar int ClassLessonResult[classes][lessons] ;
dvar int RoomLessonResult[rooms][lessons];
dvar int TeacherClassResult [teachers][classes];
dvar int RoomClassResult [rooms][classes];
dvar int RoomTeacherResult [rooms][teachers];


dvar int schedule [rooms][teachers][classes][lessons] in 0..1;
 		

minimize 
staticLex(	
 sum(c in classes, l in lessons) (  ClassLessonResult [c][l] * l  )
   ,
sum(t in teachers, l in lessons) (  TeacherLessonResult [t][l] * l  )
,
sum(r in rooms, t in teachers, c in classes, l in lessons) schedule[r][t][c][l] * roomTeachersRelation[r][t]
   )
;


 subject to
{
	 forall(
	 	r in rooms, 
	 	t in teachers, 
	 	c in classes, 
	 	l in lessons 
	 	)
	 	if(roomTeachersRelation[r][t] == 0 || teacherClassRelation[t][c] == 0 || classLessonRelation[c][l] == 0 || teacherLessonRelation[t][l] == 0)
	 	{
	   		schedule[r][t][c][l] == 0;
	   	}   		
   
	// teacher - class relations
	forall( t in teachers, c in classes) 
		sum(r in rooms, l in lessons)
			schedule[r][t][c][l] == teacherClassRelation[t][c];   
			
	forall( t in teachers, c in classes) 		
		TeacherClassResult[t][c] == sum(r in rooms, l in lessons) schedule[r][t][c][l];
	     
	 // room - lesson relations
	 forall(r in rooms, l in lessons)
		sum(t in teachers, c in classes)
			schedule[r][t][c][l] <= 1;
	       
	 forall(r in rooms, l in lessons)
		RoomLessonResult[r][l] == sum(t in teachers, c in classes) schedule[r][t][c][l]  ;
	            
	// teacher - lesson relations
	  forall( t in teachers, l in lessons)   
	  	sum(r in rooms, c in classes) 
	  		schedule[r][t][c][l] <= 1;
	  		
	forall( t in teachers, l in lessons)   
		TeacherLessonResult[t][l] == ( sum(r in rooms, c in classes)  schedule[r][t][c][l] ) ;
	  			
	  	// class - lesson relations
	forall( c in classes, l in lessons )   
	  	sum(r in rooms, t in teachers : t not in foreignLangTeachers) 
	  		schedule[r][t][c][l] <= 1;
	  		
	forall( c in classes, l in lessons )   
	  	sum(r in rooms, t in teachers : t in foreignLangTeachers) 
	  		schedule[r][t][c][l] <= 2;
	  		
	forall( c in classes, l in lessons )   
	  	sum(r in rooms, t in teachers : t not in trudyTeachers) 
	  		schedule[r][t][c][l] <= 1;
	  		
	forall( c in classes, l in lessons )   
	  	sum(r in rooms, t in teachers : t in trudyTeachers) 
	  		schedule[r][t][c][l] <= 2;
	  		
	forall( c in classes, l in lessons )  
	{
		ClassLessonResult [c][l] == ( sum(r in rooms, t in teachers)  schedule[r][t][c][l] ) ;	
	}
	
		
	//
	forall( r in rooms, c in classes) 
		RoomClassResult[r][c]  == ( sum(l in lessons, t in teachers)  schedule[r][t][c][l] ) ;
		
	//
	forall( r in rooms, t in teachers) 
	RoomTeacherResult[r][t] == ( sum(l in lessons, c in classes)  schedule[r][t][c][l] ) ;
}  
