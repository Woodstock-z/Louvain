
'''
2019/3/12
louvain算法实现
参考 Fast unfolding of communities in large networks
带权网络 修改时间2019/3/21
'''
from operator import itemgetter, attrgetter
import pymysql
import collections
import string
import random
import time

class Louvain:
	def __init__(self, nodes, edges,m):
		self.nodes=nodes
		self.edges=edges
		self.m=m
		#节点内度
		self.node_inner_degree=[0 for node in nodes]
		#节点度
		self.node_degree=[0 for node in nodes]
		self.node_com=[node for node in nodes]
		_edges={}
		for e in edges: 
			self.node_degree[e[0][0]]+=e[1]
			self.node_degree[e[0][1]]+=e[1]
			if e[0][0] in _edges:
				_edges[e[0][0]].append((e[0][1],e[1]))
			else:
				_edges[e[0][0]]=[(e[0][1],e[1])]
			if e[0][1] in _edges:
				_edges[e[0][1]].append((e[0][0],e[1]))
			else:
				_edges[e[0][1]]=[(e[0][0],e[1])]
		self.node_edges=_edges
		self.actual_com=[]
		self.ss=0
	#提前计算出每个社区的sigma_in sigma_tot
	def make_init(self):
		#每个社区的sigma_in 初始为每个节点的内度*2
		self.sigma_in=[self.node_inner_degree[node]*2 for node in self.nodes]
		#为每个节点的度
		self.sigma_tot=[self.node_degree[node] for node in self.nodes]
		now_com=[[node] for node in self.nodes]		
		return now_com
	def get_neighbors(self,node):
		neighbors=set()
		try:
			zz=self.node_edges[node]
		except KeyError:
			#该node节点没有邻居
			return neighbors
		for e in zz:
			neighbors.add(e[0])
		return neighbors
	#按节点的度进行访问
	def get_sequence(self):
		sequence=[]
		for node in self.nodes:
			sequence.append((node,self.node_degree[node]))
		s=sorted(sequence, key=itemgetter(1), reverse=False)
		se=[i[0] for i in s]
		return se
	#算法的第一个阶段
	def first_pp(self):
		print("1st---------------------------------")
		#当前社区划分情况
		now_com=self.make_init()
		final=True #算法终止信号
		counter=0
		while  True:
			print(counter)
			counter+=1
			can_stop=True 
			visit_sequence=self.get_sequence()
			# visit_sequence=self.nodes.copy()
			# random.shuffle(visit_sequence)
			for node in visit_sequence:
				node_c=self.node_com[node]	#当前节点所在社区
				max_Q=0
				best_share=0
				join_c=node_c
				inshare_link=0
				try:
					#节点可能没有邻居
					zz=self.node_edges[node]
				except KeyError:
					continue
				for e in zz:
					#e[0] e[1]
					if self.node_com[e[0]]==node_c:
					#同一个社区
						inshare_link+=e[1]
					
				#如果把当前节点移除社区 带来的模块度增益
				Q1=-2*inshare_link-2*self.node_inner_degree[node]+self.sigma_tot[node_c]*self.node_degree[node]/self.m-self.node_degree[node]**2/(2*self.m)
				#print("节点",node,"Q1",Q1)
				neighbors=self.get_neighbors(node) #节点node 的邻居
				visited_com=set()
				for nei in neighbors:
					nei_c=self.node_com[nei] #邻居节点所在社区
					if nei_c in visited_com or nei_c==node_c:
						#已经尝试过或本来就是一个社区
						continue
					visited_com.add(nei_c)
					outshare_link=0
					for e in self.node_edges[node]:
						if self.node_com[e[0]]==nei_c:
							outshare_link+=e[1]
					#如果将节点加入其邻居所在的社区所带来的模块度增益
					Q2=2*outshare_link+2*self.node_inner_degree[node]-self.sigma_tot[nei_c]*self.node_degree[node]/self.m-self.node_degree[node]**2/(2*self.m)
					# print("邻居",nei,"Q2",Q2)
					# print('outshare_link,self.node_inner_degree[node],self.sigma_tot[nei_c],self.node_degree[node]')
					# print(outshare_link,self.node_inner_degree[node],self.sigma_tot[nei_c],self.node_degree[node])
					Q=Q1+Q2
					if Q>max_Q:
						max_Q=Q
						best_share=outshare_link
						join_c=nei_c
				if max_Q>1e-8:
					can_stop=False
					final=False
					#将节点加入join_c 社区
					#改变原本社区的所有值
					now_com[node_c].remove(node)
					now_com[join_c].append(node)
					self.node_com[node]=join_c
					self.sigma_in[node_c]-=2*(inshare_link+self.node_inner_degree[node])
					self.sigma_tot[node_c]-=self.node_degree[node]
					#改变新社区的相关值
					self.sigma_in[join_c]+=2*(best_share+self.node_inner_degree[node])
					self.sigma_tot[join_c]+=self.node_degree[node]
			if can_stop:
				return final,now_com
	#算法的第二个阶段
	def second_pp(self,coms):
		self.ss=1
		print("2nd----------------------------------")
		#将社区抽象为节点
		n_nodes=[i for i in range(len(coms))]
		#为社区编号
		com_code={}
		i=0
		for com in coms:
			for c in com:
				com_code[c]=i
			i+=1
		n_node_inner_degree=[0 for node in n_nodes]
		for nod in self.nodes:
			n_nod=com_code[nod]
			n_node_inner_degree[n_nod]+=self.node_inner_degree[nod]
		edges_={}
		for e in self.edges:
			com1=com_code[e[0][0]]
			com2=com_code[e[0][1]]
			if com1==com2:
				#同一个社区
				n_node_inner_degree[com1]+=e[1]
				continue
			if com1<com2:
				try:  
					edges_[(com1, com2)] += e[1]  
				except KeyError:  
					edges_[(com1, com2)] = e[1] 
			else:
				try:  
					edges_[(com2, com1)] += e[1]  
				except KeyError:  
					edges_[(com2, com1)] = e[1]
		edges_=[(x,y) for x,y in edges_.items()]
		node_edges_={}
		self.node_degree=[2*n_node_inner_degree[node] for node in n_nodes]
		for e in edges_:
			self.node_degree[e[0][0]]+=e[1]
			self.node_degree[e[0][1]]+=e[1]
			if e[0][0] in node_edges_:
				node_edges_[e[0][0]].append((e[0][1],e[1]))
			else:
				node_edges_[e[0][0]]=[(e[0][1],e[1])]
			if e[0][1] in node_edges_:
				node_edges_[e[0][1]].append((e[0][0],e[1]))
			else:
				node_edges_[e[0][1]]=[(e[0][0],e[1])]
		self.nodes=n_nodes
		self.edges=edges_
		self.node_inner_degree=n_node_inner_degree
		self.node_edges=node_edges_
		self.node_com=[node for node in n_nodes]
	#
	def get_modularity(self):
		q=0
		m=2*self.m
		for i in range(len(self.sigma_tot)):
			q+=(self.sigma_in[i]-self.sigma_tot[i]**2/m)/m
		return q

	def execute(self):
		while 1:
			final,coms=self.first_pp()
			print(final)
			if final:
				break
			coms=[c for c in coms if c]
			if self.actual_com:

				#非第一次  coms中的节点代表着self.actual_coms对应的社区
				actual=[]
				for com in coms:
					temp=[]
					for node in com:
						temp.extend(self.actual_com[node])
					actual.append(temp)
				self.actual_com=actual
			else:
				self.actual_com=coms
			self.second_pp(coms)
		actual_len=[len(com) for com in self.actual_com]
		actual_len.sort()
		#print(actual_len)
		#print(self.actual_com)
		#print(len(self.actual_com))
		print(self.get_modularity())
		#print(self.edges)
		return self.edges

def in_order(nodes,edges):

	nodes=list(nodes)
	nodes.sort()  
	i = 0  
	nodes_ = []  
	d = {}  
	for n in nodes:  
		nodes_.append(i)  
		d[n] = i  
		i += 1  
	edges_ = []  
	for e in edges:  
		edges_.append(((d[e[0][0]], d[e[0][1]]), e[1]))  
	return (nodes_, edges_) 

def main():
	start=time.time()
	tt=[0 for i in range(148619)]
	duration=[0 for i in range(148619)]
	m=0
	nodes=set()
	edges=[]
	db = pymysql.connect("localhost","zz","123456","unicom" )
	cursor = db.cursor()
	cursor.execute("select code,times,duration from phone")
	results = cursor.fetchall()
	for item in results:
		code=int(item[0])
		times=int(item[1])
		dura=int(item[2])
		tt[code]=times
		duration[code]=dura
	cursor.execute("select code1,code2,times,duration from phone_call_edges")
	#cursor.execute("select e1,e2 from edges")
	results = cursor.fetchall()
	for item in results:
		if(item[0]==item[1]):
			continue
		a=2*int(item[2])/(tt[int(item[0])]+tt[int(item[1])])
		b=2*int(item[3])/(duration[int(item[0])]+duration[int(item[1])])
		m+=(a+b)
		nodes.add(int(item[0]))
		nodes.add(int(item[1]))
		edges.append(((int(item[0]),int(item[1])),a+b))
	_nodes,_edges=in_order(nodes,edges)
	print(m)
	print(time.time()-start)
	louvain=Louvain(_nodes,_edges,m)
	edges=louvain.execute()
	# for e in edges:
	# 	com1=e[0][0]
	# 	com2=e[0][1]
	# 	value=e[1]
	# 	sql="insert into com_edges values("+str(com1)+","+str(com2)+","+str(value)+")"
	# 	cursor.execute(sql)
	# db.commit()



if __name__ == '__main__':
	main()