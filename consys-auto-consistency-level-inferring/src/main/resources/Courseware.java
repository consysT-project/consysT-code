class Enrolment {
    final Student student;
    final Course course;
}

@Invariant("forall r ∈ enrolments. exists s ∈ students, c ∈ courses. r.student = s && r.course = c ")
class Courseware {
    Set<Student> students = Sets.newHashset();
    Set<Course> courses = Sets.newHashset();
    Set<Enrolment> enrolments = Sets.newHashset();

    @PostCond("new.students == this.students ∪ {student}")
    @Op void register(Student student) {
        students.add(student);
    }

    @PostCond("new.courses == this.courses ∪ {course}")
    @Op void addCourse(Course course) {
        courses.add(course);
    }

    @PostCond("new.enrolments == this.enrolments ∪ {{student := student, course = course}}")
    @Op void enroll(Student student, Course course) {
        enrolments.add(new Enrolment(student, course));
    }

    @PreCond("forall r ∈ enrolments. r.course != course")
    @PostCond("new.courses == this.courses intersect {course}")
    @Op void deleteCourse(Course course) {
        courses.remove(course);
    }

    @PostCond("new.students == this.students ∪ other.students && new.courses = this.courses ∪ other.courses && new.enrolments = this.enrolments ∪ other.enrolments")
            @Merge void merge(Courseware other) {
        students.addAll(other.students);
        courses.addAll(other.courses);
        enrolments.addAll(other.enrolments);
    }
}