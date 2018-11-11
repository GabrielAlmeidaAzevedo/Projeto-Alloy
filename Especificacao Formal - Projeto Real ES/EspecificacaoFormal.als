module spottedApp
--Actions are composed with verb.

one sig SpottedApp {
  usuarios: set Usuario,
  admin: one Admin
}

sig Admin{
  visualizaDenuncia: set Post
}

sig Username{}
abstract sig Login {}
sig Google extends Login {}
sig Facebook extends Login {}

sig Perfil {
  login: one Login,
  username: one Username
}

sig Usuario {
  perfil: one Perfil,
  editarPerfil: one Perfil,
  posts: set Post,
  excluiPost: set Post,
  visualizaPost: set Post,
  pesquisaPost: set Post,
  denunciaPost: lone Post
}

sig Comentario{
  dono: one Usuario,
  notificaUsuario: one Usuario,
  editarComentario: one Usuario,
  apagarComentario: one Usuario
}

abstract sig Post {
	comentarios: set Comentario
}
sig Spotted extends Post {}
sig Aviso extends Post {}
sig Noticia extends Post {}
sig Evento extends Post {}
sig Entreterimento extends Post {}

fact FatosGeraisUsuario{
    -- As instancias possuim diferentes donos. Usuario visualiza todos os posts
    -- Usuario pesquisa por uma quantidade menor de posts.
    -- Usuario pode excluir apenas seus post
    -- Usuario edita o proprio perfil. Usuario nao pode denuncia um post seu.
    all u1:Usuario | all u2:Usuario | (u1 != u2) =>  (u1.posts != u2.posts)
    all u1:Usuario | all u2:Usuario | (u1 != u2) =>  (u1.perfil != u2.perfil)
    all u:Usuario | #(u.visualizaPost) = #Post
    all u:Usuario | #(u.pesquisaPost) < #Post
    all u:Usuario | (u.posts&u.excluiPost) = u.excluiPost
    all u:Usuario | u.perfil = u.editarPerfil
    all u:Usuario | u.posts != u.denunciaPost
}

fact FatosGeraisComentario{ 
	-- As instancias possuim diferentes donos. Usuario nao se notifica;
	-- Apenas o dono do comentario pode editar e apagar ele.
  	all p1:Post | all p2:Post | (p1 != p2) =>  (p1.comentarios != p2.comentarios)
  	all c:Comentario | c.dono != c.notificaUsuario
	all c:Comentario | c.dono = c.apagarComentario
	all c:Comentario | c.dono = c.editarComentario
}

fact FatosGeraisPerfil{ -- As instancias possuim diferentes donos
  all p1:Perfil | all p2:Perfil | (p1 != p2) =>  (p1.username != p2.username)
  all p1:Perfil | all p2:Perfil | (p1 != p2) =>  (p1.login != p2.login)
}

fact FatosGeraisPost{ -- As denuncias estao contidas no set de visualizaDenuncia
  all u:Usuario | all a:Admin | (a.visualizaDenuncia&u.denunciaPost) = u.denunciaPost
}

fact FatsExistencias{ --Todo instancia esta ligada a uma sig
    all u:Usuario| one u.~usuarios
    all a:Admin| one a.~admin
    all u:Username| one u.~username
    all p:Post| one p.~posts
    all p:Perfil| one p.~perfil
    all l:Login| one l.~login
    all c:Comentario| one c.~comentarios
}

assert Testes{}

pred show[]{}
run show for 5
