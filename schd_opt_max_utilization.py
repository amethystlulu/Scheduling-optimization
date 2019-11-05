from pyomo.environ import *
import psycopg2
import psycopg2.extras
import numpy as np
import pandas as pd
from pandas import Series,DataFrame
import urllib
import json
import operator
import ast
import random
class SCHD_OPT(object):
    results = {}
    
    def __init__(self):
        self.model = ConcreteModel()
        self.runtime = 0
    
    ##########################################
    ######### construct model ################
    ##########################################
    def construct_model(self, sq, mech_cal):
        model = self.model
        ########## initial parameters ##########
        # number of mechanics
        model.num_M = Param(within=PositiveIntegers, mutable=True, initialize = len(mech_cal))

        # morning rush hours start/end
        model.rh1 = Param(within=PositiveIntegers, mutable=True, initialize=24)
        model.rh2 = Param(within=PositiveIntegers, mutable=True, initialize=39)

        # evening rush hours start/end
        model.rh3 = Param(within=PositiveIntegers, mutable=True,initialize=60)
        model.rh4 = Param(within=PositiveIntegers, mutable=True,initialize=75)

        # upper bound of number of time slots
        model.U = Param(within=PositiveIntegers, mutable=True,initialize=96)

        # minutes/mile in normal hour
        model.NormalMPM = Param(within=PositiveReals, mutable=True,initialize=2.5)

        # minutes/mile in rush hour
        model.RushHourMPM = Param(within=PositiveReals, mutable=True,initialize=4.0)

        ############### sets #############
        # mechanics
        model.M = RangeSet(0, model.num_M-1)

        #timeslots
        model.S = RangeSet(28,83, ordered=True)

        #jobs
        model.J = Set(initialize = RangeSet(0, len(sq)-1))

        # (j1, j2) for j1 in J and j2 in J and j1 <> j2
        excld = set([(j,j) for j in model.J])
        model.Excld = Set(dimen =2, initialize = excld)
        model.JJ = (model.J * model.J) - model.Excld


        ########## paramters based on sets ###############
        # mechanic calendar [m,s]
        def find_mech_cal(model, m, s):
            return mech_cal.loc[m,s]
        model.mech_cal = Param(model.M, model.S, within=Binary,mutable = True, rule=find_mech_cal)

        ######### variables crossing jobs ###############
        # tau[j1, j2] = travel minutes between job j1 and j2
        model.tau = Var(model.JJ, within = NonNegativeReals)

        # v[j1, j2, m] = 1 if job j1 and job j2 are both assigned to mech m, and j1 starts BEFORE j2
        model.v = Var(model.JJ, model.M, within=Binary)

        ###### blocks
        def job_block_rule(b, j):
            #### define the variables
            b.y = Var(model.M, model.S, within=Binary)  # y_jms = 1 if job j is assigned to mech m to start from slot s
            b.z = Var(model.M, model.S, within=Binary)  # z_jms = 1 if job j uses slot s of mech m
            b.c = Var(within=NonNegativeReals) # c_j =  starting slot of job j
            b.alpha = Var(within=Binary) # alpha_j = 1 if job j's ending time slot >= 24
            b.beta = Var(within=Binary) # beta_j = 1 if job j's ending time slot <= 39
            b.gamma = Var(within=Binary) # gamma_j = 1 if job j's ending time slot >= 60
            b.theta = Var(within=Binary) # gamma_j = 1 if job j's ending time slot <= 75
            b.r = Var(within=Binary) # r_j = 1 if job j ends in rush hour
            #### define the constraints
            # (1) each job is only assigned to one mechanic to start in one time slot
            def _assignment_rule(_b):
                return sum([_b.y[m,s] for m in model.M for s in model.S]) <= 1
            b.assignment_constraint = Constraint(rule=_assignment_rule)

            # (2) if job j is assigned to m to start from slot s, mech m must be available at s
            def _start_slot_available_rule(_b, m, s):
                return _b.y[m,s] - model.mech_cal[m,s] <= 0
            b.slot_available_constraint = Constraint(model.M, model.S, rule=_start_slot_available_rule)

            # (3) if job j is assigned to m to start from slot s, mech m must be available for the entire duration of job j
            def _dur_available_rule(_b, m, s, ss):
            #if ss in range(s, s + int(model.schedule_slots[j])):
            #if (ss>=s) & (ss - s < value(model.schedule_slots[j])): # ok
                if (ss>=s) & (ss - s < sq[j]['schedule_slots']):
                    return _b.z[m,ss] - _b.y[m,s] >= 0
                else:
                    return Constraint.Skip
            b.dur_available_constraint = Constraint(model.M, model.S, model.S, rule = _dur_available_rule)

            # (3') the total time slots that a job uses must not exceed its schedule_slots
            def _total_slots_rule(_b):
                return sum([_b.z[m,s] for m in model.M for s in model.S]) <= sq[j]['schedule_slots']
            b.total_slots_constraint = Constraint(rule = _total_slots_rule)

            # (4') mechanic qualification: mech m must be qualified to do job j if j is assigned to m
            def _mechanic_qualification_rule(_b, m, s):
                return _b.z[m,s] - sq[j]['match'][m] <= 0
            b.mechanic_qualification_constraint = Constraint(model.M, model.S, rule = _mechanic_qualification_rule)

            # (5) starting slot of job j
            def _starting_slot_rule(_b):
                return sum([s * _b.y[m,s] for s in model.S for m in model.M]) - _b.c == 0
            b.starting_slot_constraint = Constraint(rule = _starting_slot_rule)

            #(5') ending slot of job j does not exceed the end of day (9 pm)
            b.ending_slot_constraint = Constraint(expr = b.c + sq[j]['schedule_slots'] - 1 <= model.S.last())


            #(6) and (6') check if ending slot of job j is >= 24
            b.ending_slot_after_rh1_first = Constraint(expr = b.c + sq[j]['schedule_slots'] - 1 - (model.rh1-1) <= model.U * b.alpha)
            b.ending_slot_after_rh1_second = Constraint(expr = b.c + sq[j]['schedule_slots'] - 1 - model.rh1 >= -model.U * (1-b.alpha))

            #(7) and (7') check if ending slot of job j is <= 39
            # 40 - e <= 96*beta is equivalent to 39 - e < 96*beta
            b.ending_slot_after_rh2_first = Constraint(expr = model.rh2 + 1 - (b.c + sq[j]['schedule_slots'] - 1) <= model.U * b.beta)
            b.ending_slot_after_rh2_second = Constraint(expr = model.rh2 - (b.c + sq[j]['schedule_slots'] - 1) >= -model.U * (1-b.beta))

            # (8) and (8') check if ending slot of job j is >= 60
            b.ending_slot_after_rh3_first = Constraint(expr = b.c + sq[j]['schedule_slots'] - 1 - (model.rh3-1) <= model.U * b.gamma)
            b.ending_slot_after_rh3_second = Constraint(expr = b.c + sq[j]['schedule_slots'] - 1 - model.rh3 >= -model.U * (1-b.gamma))

            #(9) and (9') check if ending slot of job j is <= 75
            b.ending_slot_after_rh4_first = Constraint(expr = model.rh4 + 1 - (b.c + sq[j]['schedule_slots'] - 1) <= model.U * b.theta)
            b.ending_slot_after_rh4_second = Constraint(expr = model.rh4 - (b.c + sq[j]['schedule_slots'] - 1) >= -model.U * (1-b.theta))

            # (10) and (10') check if job j ends in rush hours
            b.ends_in_morning_rh = Constraint(expr = b.r >= b.alpha + b.beta - 1)
            b.ends_in_evening_rh = Constraint(expr = b.r >= b.gamma + b.theta - 1)
            
            # (15) and (15') selected time range lower bound and upper bound
            b.time_range_upper_bound = Constraint(expr = b.c - 96 <= 0)
            b.time_range_lower_bound = Constraint(expr = b.c >= 0)

        # claim blocks    
        model.jobb = Block(model.J, rule = job_block_rule)


        #### objective function
        def obj_rule(model):
            return sum(sq[j]['schedule_minutes'] * model.jobb[j].y[m,s] for j in model.J for m in model.M for s in model.S)
        model.obj = Objective(rule=obj_rule, sense=maximize)

        # ##### linking constraints
        # (4) each time slot for each mech can only be assigned to at most one job
        def at_most_one_job_per_mech_slot_rule(model, m, s):
            return sum([model.jobb[j].z[m,s] for j in model.J]) - model.mech_cal[m,s] <= 0
        model.at_most_one_job_per_mech_slot_constraint = Constraint(model.M, model.S, rule = at_most_one_job_per_mech_slot_rule)


        # (11) travel time between job j1 and job j2
        def distance(lat1, lon1, lat2 ,lon2):
            MILES_PER_DEGREE = 69.09  #1.1515*60.0
            coslat = np.cos(0.5*(lat2+lat1))
            return np.sqrt((lat1-lat2)*(lat1-lat2)+(lon1-lon2)*(lon1-lon2)*coslat*coslat)*MILES_PER_DEGREE

        def travel_time_between_jobs_rule(model, j1, j2):
            d = distance(sq[j1]['latitude'], sq[j1]['longitude'], sq[j2]['latitude'], sq[j2]['longitude'])
            return model.tau[j1,j2] - (model.NormalMPM * d + (model.RushHourMPM - model.NormalMPM) * d * model.jobb[j1].r) == 0

        model.travel_time_between_jobs_constraint = Constraint(model.JJ, rule = travel_time_between_jobs_rule)

        # (12) and (12') if both j1 and j2 are assigned to mech m, then j1 and j2 must be assigned to m, respectively
        def assign_j1_rule(model, j1, j2, m):
            return model.v[j1, j2, m] - sum(model.jobb[j1].y[m,s] for s in model.S) <= 0
        model.assign_j1_constraint = Constraint(model.JJ, model.M, rule = assign_j1_rule)

        def assign_j2_rule(model, j1, j2, m):
            return model.v[j1, j2, m] - sum(model.jobb[j2].y[m,s] for s in model.S) <= 0
        model.assign_j2_constraint = Constraint(model.JJ, model.M, rule = assign_j2_rule)

        # (13) and (13') if j1 and j2 are both assigned to m, there must be only one order between the starting times of j1 and j2.
        def j1_j2_order_ub_rule(model, j1, j2, m):
            return model.v[j1, j2, m] + model.v[j2, j1, m] <= 1
        model.j1_j2_order_ub_constraint = Constraint(model.JJ, model.M, rule = j1_j2_order_ub_rule)

        def j1_j2_order_lb_rule(model, j1, j2, m):
            return model.v[j1, j2, m] + model.v[j2, j1, m] >= sum(model.jobb[j1].y[m,s] for s in model.S) + sum(model.jobb[j2].y[m,s] for s in model.S) -1
        model.j1_j2_order_lb_constraint = Constraint(model.JJ, model.M, rule = j1_j2_order_lb_rule)

        #(14') if job j1 and job j2 are both assigned to m, and j1 starts before j2,
            #then v_j1_j2_m = 1 and v_j2_j1_m = 0,
            #and there must be enough travel time between completion of j1 and beginning of j2

        def j2_after_j1_travel_time_rule(model, j1, j2, m):
            return sum(s * model.jobb[j2].y[m,s] for s in model.S) - sum(s * model.jobb[j1].y[m,s] for s in model.S) - (sq[j1]['schedule_minutes'] + model.tau[j1, j2])/15.0 >= -2 * model.U * (1-model.v[j1, j2, m])
        model.j2_after_j1_travel_time_rule = Constraint(model.JJ, model.M, rule = j2_after_j1_travel_time_rule)
    
        
    ################################################################
    ############### add time range lb and ub for job j #############
    ################################################################
    # timerange[0] = lb of selected time range to start the job
    # timerange[1] = ub of selected time range to start the job
    def add_time_range(self, j, timerange):
        # add upper bound (modify time_range_upper_bound constraint)
        self.model.jobb[j].time_range_upper_bound._body = self.model.jobb[j].c - timerange[1]
        
        # add lower bound (modify time_range_lower_bound constraint)
        def e_rule(b):
            return b.c - sum (b.y[m,s] for m in self.model.M for s in self.model.S) * timerange[0]
        self.model.jobb[j].e = Expression(rule = e_rule)
        self.model.jobb[j].time_range_lower_bound._body = self.model.jobb[j].e

    def job_must_be_assigned(self, j):
        self.model.jobb[j].assignment_constraint._lower = 1

    def job_fix_mech(self, j, m):
        for m in self.model.M - set([m]):
            for s in self.model.S:
                self.model.jobb[j].y[m,s].setub(0)
    
    #################################################
    ############### solve problem ###################
    ##################################################
    def solve_model(self):
        solver = SolverFactory('cplex')
        self.results = solver.solve(self.model)
        self.runtime += self.results['Solver'][0]['User time']




