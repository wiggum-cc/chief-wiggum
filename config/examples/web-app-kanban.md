# Web Application Kanban

## TASKS

- [ ] **[TASK-001]** Setup FastAPI backend
  - Description: Create FastAPI app with basic structure, CORS middleware, and health endpoint
  - Priority: HIGH
  - Dependencies: none

- [ ] **[TASK-002]** Setup database with SQLAlchemy
  - Description: Configure SQLAlchemy, create database models for users and posts
  - Priority: HIGH
  - Dependencies: none

- [ ] **[TASK-003]** Implement user authentication
  - Description: Add JWT-based authentication endpoints (register, login, logout)
  - Priority: HIGH
  - Dependencies: TASK-001, TASK-002

- [ ] **[TASK-004]** Create React frontend
  - Description: Setup React app with Vite, basic routing, and component structure
  - Priority: MEDIUM
  - Dependencies: none

- [ ] **[TASK-005]** Implement CRUD API for posts
  - Description: Create, read, update, delete endpoints for blog posts
  - Priority: MEDIUM
  - Dependencies: TASK-001, TASK-002, TASK-003

- [ ] **[TASK-006]** Add Docker configuration
  - Description: Create Dockerfile and docker-compose.yml for backend, frontend, and PostgreSQL
  - Priority: LOW
  - Dependencies: TASK-001, TASK-002, TASK-004
