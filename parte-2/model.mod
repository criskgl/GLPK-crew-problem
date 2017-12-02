#DECLARACIÓN DE CONJUNTOS PROBLEMA COMPARTIMENTOS-------------------------------------------------------

set MALETAS;				#{m} Conjunto de maletas (3)

set COMPARTIMENTOS;			#{c} Conjunto de compartimentos (6)

set COMPARTIMENTOS_DELANTEROS within COMPARTIMENTOS; #{cd} Conjunto Compartimentos delanteros

set COMPARTIMENTOS_TRASEROS within COMPARTIMENTOS; #{ct} Conjunto Compartimentos delanteros

set CARACTERISTICAS_M;			#{km} Conjunto de caracteristicas de las maletas 

set CARACTERISTICAS_C;			#{kc} Conjunto de caracteristicas de los compartimentos 


#DECLARACIÓN DE CONJUNTOS PROBLEMA VUELOS----------------------------------------------------------------

set VUELOS;				#{v} Conjunto de vuelos (6)

set VUELOS_IDA within VUELOS;			#{vi} Conjunto de vuelos de ida (3)

set VUELOS_VUELTA within VUELOS;		#{vv} Conjunto de vuelos de ida (3)

set TRIPULACION; 						#{t} Conjunto de miembros de la tripulación(6)

set PILOTOS within TRIPULACION;			#{p} Conjunto de pilotos(3)

set AUXILIARES within TRIPULACION;			#{a} Conjunto de auxiliares(3)

set CARACTERISTICAS_P_DESCANSO;   #{kpd} descanso de cada piloto

set CARACTERISTICAS_V;	#{kv} Conjunto de caracteristicas de los vuelos

#DECLARACION DE PARÁMETROS PROBLEMA COMPARTIMENTOS-------------------------------------------------------

param caracteristicas_m{km in CARACTERISTICAS_M, m in MALETAS};
param caracteristicas_c{kc in CARACTERISTICAS_C, c in COMPARTIMENTOS};

#DECLARACION DE PARÁMETROS PROBLEMA VUELOS---------------------------------------------------------------

param pagos_trip{t in TRIPULACION, v in VUELOS};
param descanso_piloto{p in PILOTOS, kpd in CARACTERISTICAS_P_DESCANSO};

param duracion_vuelos{v in VUELOS, kv in CARACTERISTICAS_V};
param t_entre_vuelos{vi in VUELOS, vj in VUELOS};

#VARIABLES DECISION PROBLEMA COMPARTIMENTOS--------------------------------------------------------------

var x{c in COMPARTIMENTOS, m in MALETAS} integer, >=0; 
#Unidades de maletas de tipo m en compartimento c

#VARIABLES DECISION PROBLEMA VUELOS--------------------------------------------------------------

var y{t in TRIPULACION, v in VUELOS} binary; 
#tripulante t va en vuelo v(0="no", 1="si")

#OBJETIVO---------------------------------------------------------------------------------------------------------

minimize total_cost: (sum{m in MALETAS}((caracteristicas_m['uds', m] - sum{c in COMPARTIMENTOS} x[c, m])*caracteristicas_m['coste', m]))+(sum{t in TRIPULACION}(sum{v in VUELOS}(y[t, v]*(pagos_trip[t, v]/60)*duracion_vuelos[v, 'duracion'])));

						#RESTRICCIONES PROBLEMA COMPARTIMENTOS#

#################Peso delantero(comp1 y comp4) 1,3 veces mayor al menos que trasero(comp3, comp6)#################
s.t. Peso_delantero_mayor{cd in COMPARTIMENTOS_DELANTEROS, ct in COMPARTIMENTOS_TRASEROS}: 
sum{m in MALETAS}(x[cd, m]+x[cd,m]*caracteristicas_m['peso', m])
>=
1.1*(sum{m in MALETAS}(x[ct, m]+x[ct,m]*caracteristicas_m['peso', m]));

############################Peso Maximo de cada compartimento#####################################################
s.t. Peso_max_por_compartimento{c in COMPARTIMENTOS}: sum{m in MALETAS}x[c, m] * caracteristicas_m['peso', m] <= caracteristicas_c['peso', c]; 


##############################Volumen Maximo de cada compartimento#################################################
s.t. Vol_max_por_compartimento{c in COMPARTIMENTOS}: sum{m in MALETAS}x[c, m] * caracteristicas_m['vol', m] <= caracteristicas_c['vol', c]; 

##############################Uds Maximas de cada maleta#################################################
s.t. Uds_max_de_maletas{m in MALETAS}: sum{c in COMPARTIMENTOS}x[c, m]<=caracteristicas_m['uds', m];

						#RESTRICCIONES PROBLEMA VUELOS#

#TRIPULACION MINIMA
s.t. min_trip_piloto{v in VUELOS}: sum{p in PILOTOS} y[p, v] >= 1;
s.t. min_trip_auxiliar{v in VUELOS}: sum{a in AUXILIARES} y[a, v] >= 1;

#PILOTOS VUELAN MENOS HORAS QUE AUXILIARES

s.t. auxiliares_trabajan_mas: sum{i in PILOTOS, v in VUELOS}(y[i, v]*duracion_vuelos[v,'duracion']) <=  sum{c in AUXILIARES, v in VUELOS}(y[c,v]*duracion_vuelos[v,'duracion']);

#LOCALIZACION DE PILOTOS-->SOLO 0 ó 1 

s.t. localizacion_piloto_M{p in PILOTOS, v in VUELOS}: sum{vida in VUELOS_IDA: vida <= v}y[p, vida]-sum{vta in VUELOS_VUELTA: vta <= v}y[p, vta] <= 1;

s.t. localizacion_piloto_V{p in PILOTOS, v in VUELOS}: sum{vida in VUELOS_IDA: vida <= v}y[p, vida]-sum{vta in VUELOS_VUELTA: vta <= v}y[p, vta] >= 0;

s.t. localizacion_auxiliar_M{a in AUXILIARES, v in VUELOS}: sum{vida in VUELOS_IDA: vida <= v}y[a, vida]-sum{vta in VUELOS_VUELTA: vta <= v}y[a, vta] <= 1;

s.t. localizacion_auxiliar_V{a in AUXILIARES, v in VUELOS}: sum{vida in VUELOS_IDA: vida <= v}y[a, vida]-sum{vta in VUELOS_VUELTA: vta <= v}y[a, vta] >= 0;


#RESPETAR DESCANSOS CONSECUTIVOS PARA LOS PILOTOS
s.t. descansos_p{p in PILOTOS, vllego in VUELOS, vvoy in VUELOS: vllego < vvoy}: t_entre_vuelos[vllego,vvoy] >= descanso_piloto[p, 'descanso']*(y[p,vllego]+y[p,vvoy]-1) ;


end;

