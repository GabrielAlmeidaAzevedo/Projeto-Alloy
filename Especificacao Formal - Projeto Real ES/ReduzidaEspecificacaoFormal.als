module spottedApp
one sig SpottedApp {
  usuarios: set Usuario
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
}
abstract sig Post {}
sig Spotted extends Post {}
sig Aviso extends Post {}
sig Noticia extends Post {}
sig Evento extends Post {}
sig Entreterimento extends Post {}
fact FatosGeraisUsuario {
    all u1:Usuario | all u2:Usuario | (u1 != u2) =>  (u1.posts != u2.posts)
    all u1:Usuario | all u2:Usuario | (u1 != u2) =>  (u1.perfil != u2.perfil)
    all u:Usuario | #(u.visualizaPost) = #Post
    all u:Usuario | #(u.pesquisaPost) < #Post
    all u:Usuario | (u.posts&u.excluiPost) = u.excluiPost
    all u:Usuario | u.perfil = u.editarPerfil
}
fact FatosGeraisPerfil {
  all p1:Perfil | all p2:Perfil | (p1 != p2) =>  (p1.username != p2.username)
  all p1:Perfil | all p2:Perfil | (p1 != p2) =>  (p1.login != p2.login)
}
fact FatosExistencias {
    all u:Usuario| one u.~usuarios
    all u:Username | one u.~username
    all p:Post | one p.~posts
    all p:Perfil | one p.~perfil
    all l:Login | one l.~login
}
pred show[]{}
run show for 5
