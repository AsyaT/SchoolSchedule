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

dvar int TeacherLessonResult[teachers][lessons] ;
dvar int ClassLessonResult[classes][lessons] ;
dvar int RoomLessonResult[rooms][lessons];

dvar int schedule [rooms][teachers][classes][lessons] in 0..1;
 		

maximize 
sum(r in rooms, t in teachers, c in classes, l in lessons)
   schedule[r][t][c][l] * roomTeachersRelation[r][t];

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
	  	sum(r in rooms, t in teachers) 
	  		schedule[r][t][c][l] <= 1;
	  		
	forall( c in classes, l in lessons )  
		ClassLessonResult [c][l]== ( sum(r in rooms, t in teachers)  schedule[r][t][c][l] ) ;
}  
