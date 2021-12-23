/*!
  \file aig_algebraic_rewriting.hpp
  \brief AIG algebraric rewriting

  EPFL CS-472 2021 Final Project Option 1
*/

#pragma once

#include "../networks/aig.hpp"
#include "../views/depth_view.hpp"
#include "../views/topo_view.hpp"

namespace mockturtle
{

namespace detail
{

template<class Ntk>
class aig_algebraic_rewriting_impl
{
  using node = typename Ntk::node;
  using signal = typename Ntk::signal;

public:
  aig_algebraic_rewriting_impl( Ntk& ntk )
    : ntk( ntk )
  {
    static_assert( has_level_v<Ntk>, "Ntk does not implement depth interface." );
  }

  void run()
  {
    bool cont{true}; /* continue trying */
    while ( cont )
    {
      cont = false; /* break the loop if no updates can be made */
      ntk.foreach_gate( [&]( node n ){
        if ( try_algebraic_rules( n ) )
        {
          ntk.update_levels();
          cont = true;
        }
      });
    }
  }

private:
  /* Try various algebraic rules on node n. Return true if the network is updated. */
  bool try_algebraic_rules( node n )
  {
    if ( try_associativity( n ) )
      return true;
    if ( try_distributivity( n ) )
      return true;
    /* TODO: add more rules here... */

    return false;
  }

  /* Try the associativity rule on node n. Return true if the network is updated. */
  bool try_associativity( node n )
  {
    std::vector<signal> signal_lv1, signal_lv2;
    signal sig_high1, sig_low1;
    signal sig_high2, sig_low2;
    int diff;

    // Level 1
    // Extract fanins of node n and check there are exactly 2 fanins
    ntk.foreach_fanin(n, [&](signal sig){signal_lv1.push_back(sig);});
    if(signal_lv1.size() != 2)
      return false;

    // Difference of level between fanins.
    //If the difference is bigger than 2 associativity is worthy
    diff = ntk.level(ntk.get_node(signal_lv1.at(0))) - ntk.level(ntk.get_node(signal_lv1.at(1)));
    if(diff >= 2){
      sig_high1 = signal_lv1.at(0);
      sig_low1 = signal_lv1.at(1);
    } else if(diff <= -2){
      sig_high1 = signal_lv1.at(1);
      sig_low1 = signal_lv1.at(0);
    } else {
      return false;
    }

    // The node we tried to optimize should not be complemented or have more than 1 fanout
    if(ntk.is_complemented(sig_high1) || ntk.fanout_size(ntk.get_node(sig_high1)) != 1)
      return false;

    // Level 2 (fanins of fanins)
    // Extract fanins of the fanin with the highest level and check there are 2 fanins
    ntk.foreach_fanin(ntk.get_node(sig_high1), [&](signal sig){signal_lv2.push_back(sig);});
    if(signal_lv2.size() != 2)
      return false;

    if(ntk.level(ntk.get_node(signal_lv2.at(0))) >= ntk.level(ntk.get_node(signal_lv2.at(1)))){
      sig_high2 = signal_lv2.at(0);
      sig_low2 = signal_lv2.at(1);
    } else {
      sig_high2 = signal_lv2.at(1);
      sig_low2 = signal_lv2.at(0);
    }

    // OR gates instead of AND gates
    if(ntk.is_complemented(sig_high2))
      sig_low1 = !sig_low1;
    if(ntk.is_complemented(sig_low1))
      sig_high2 = !sig_high2;

    ntk.replace_in_node(n, ntk.get_node(sig_low1), sig_high2);
    ntk.replace_in_node(ntk.get_node(sig_high1), ntk.get_node(sig_high2), sig_low1);

    return true;
  }

  /* Try the distributivity rule on node n. Return true if the network is updated. */
  bool try_distributivity( node n )
  {
    std::vector<signal> signal_lv1, signal_lv2_nA, signal_lv2_nB;
    signal common, sig_in1, sig_in2;
    node A, B;
    bool find = false;

    // Extract the fanins of node n and check that there are 2 fanins
    ntk.foreach_fanin(n, [&](signal sig){signal_lv1.push_back(sig);});
    if(signal_lv1.size() != 2)
      return false;

    A = ntk.get_node(signal_lv1.at(0));
    B = ntk.get_node(signal_lv1.at(1));

    // Extract fanins of fanins and check they have 2 fanins each and exactly 1 fanout
    ntk.foreach_fanin(A, [&](signal sig){signal_lv2_nA.push_back(sig);});
    ntk.foreach_fanin(B, [&](signal sig){signal_lv2_nB.push_back(sig);});
    if(signal_lv2_nA.size() != 2 || signal_lv2_nB.size() != 2 ||
        ntk.fanout_size(A) != 1 || ntk.fanout_size(B) != 1)
      return false;

    // Is there a common fanins of fanins ?
    for(int i=0; i<2; i++){
      for(int j=0; j<2; j++){
        if(signal_lv2_nA.at(i) == signal_lv2_nB.at(j)){
          common = signal_lv2_nA.at(i);
          if(i==0){
            sig_in1 = signal_lv2_nA.at(1);
            sig_in2 = signal_lv2_nB.at(1);
          }else{
            sig_in1 = signal_lv2_nA.at(0);
            sig_in2 = signal_lv2_nB.at(0);
          }
          find = true;
        }
      }
    }

    // No common fanins of fanins try 3rd layer distributivity
    if(!find){
      if(try_three_layer_distrib(n, A, B, signal_lv2_nA, signal_lv2_nB))
        return true; //currently not working
      else
        return false;
    }else{
      invert_outputs(n);

      if(ntk.is_complemented(signal_lv1.at(0)))
        ntk.replace_in_node(n, A, !common);
      else
        ntk.replace_in_node(n, A, common);

      if(ntk.is_complemented(common))
        ntk.replace_in_node(B, ntk.get_node(common), sig_in1);
      else
        ntk.replace_in_node(B, ntk.get_node(common), !sig_in1);

      if(ntk.is_complemented(sig_in2))
        ntk.replace_in_node(B, ntk.get_node(sig_in2), sig_in2);
      else
        ntk.replace_in_node(B, ntk.get_node(sig_in2), !sig_in2);

      ntk.take_out_node(A); //Remove A node from the table

      return true;
    }
  }

  bool try_three_layer_distrib(node const&n, node A, node B, std::vector<signal> signal_lv2_nA, std::vector<signal> signal_lv2_nB)
  {
    std::vector<signal> signal_lv3;
    std::vector<signal> signal_lv2;
    signal common, sig1, sig2, sig3;
    bool is_common_A;
    bool find = true;
    node C;

    // Extract 3rd layer fanins and check there are at least 4 fanins
    ntk.foreach_fanin(ntk.get_node(signal_lv2_nA.at(0)), [&](signal sig){signal_lv3.push_back(sig);});
    ntk.foreach_fanin(ntk.get_node(signal_lv2_nA.at(1)), [&](signal sig){signal_lv3.push_back(sig);});
    ntk.foreach_fanin(ntk.get_node(signal_lv2_nB.at(0)), [&](signal sig){signal_lv3.push_back(sig);});
    ntk.foreach_fanin(ntk.get_node(signal_lv2_nB.at(1)), [&](signal sig){signal_lv3.push_back(sig);});

    if(signal_lv3.size() <= 4)
      return false;
    if(ntk.fanout_size(ntk.get_node(signal_lv2_nA.at(0))) != 1 || ntk.fanout_size(ntk.get_node(signal_lv2_nA.at(1))) != 1 ||
      ntk.fanout_size(ntk.get_node(signal_lv2_nB.at(0))) != 1 || ntk.fanout_size(ntk.get_node(signal_lv2_nB.at(1))) != 1 )
      return false;

    // Is there 3rd layer fanins common with a 2nd layer fanin ?
    for(int i=0; i<signal_lv3.size(); i++){
      if(signal_lv3.at(i) == signal_lv2_nA.at(0)){
        is_common_A = true;
        common = signal_lv2_nA.at(0);
        sig1 = signal_lv2_nA.at(1);
        ntk.foreach_fanin(ntk.get_node(signal_lv2_nB.at(0)), [&](signal sig){signal_lv2.push_back(sig);});
        if(signal_lv2.size() != 2){
          C = ntk.get_node(signal_lv2_nB.at(1));
          sig3 = signal_lv2_nB.at(0);
          signal_lv2.clear();
          ntk.foreach_fanin(ntk.get_node(signal_lv2_nB.at(1)), [&](signal sig){signal_lv2.push_back(sig);});
          if(signal_lv2.at(0) == common)
            sig2 = signal_lv2.at(1);
          else
            sig2 = signal_lv2.at(0);
        } else {
          C = ntk.get_node(signal_lv2_nB.at(0));
          sig3 = signal_lv2_nB.at(1);
          if(signal_lv2.at(0) == common)
            sig2 = signal_lv2.at(1);
          else
            sig2 = signal_lv2.at(0);
        }

      }else if(signal_lv3.at(i) == signal_lv2_nA.at(1)){
        is_common_A = true;
        common = signal_lv2_nA.at(1);
        sig1 = signal_lv2_nA.at(0);
        ntk.foreach_fanin(ntk.get_node(signal_lv2_nB.at(0)), [&](signal sig){signal_lv2.push_back(sig);});
        if(signal_lv2.size() != 2){
          C = ntk.get_node(signal_lv2_nB.at(1));
          sig3 = signal_lv2_nB.at(0);
          signal_lv2.clear();
          ntk.foreach_fanin(ntk.get_node(signal_lv2_nB.at(1)), [&](signal sig){signal_lv2.push_back(sig);});
          if(signal_lv2.at(0) == common)
            sig2 = signal_lv2.at(1);
          else
            sig2 = signal_lv2.at(0);
        } else {
          C = ntk.get_node(signal_lv2_nB.at(0));
          sig3 = signal_lv2_nB.at(1);
          if(signal_lv2.at(0) == common)
            sig2 = signal_lv2.at(1);
          else
            sig2 = signal_lv2.at(0);
        }

      }else if(signal_lv3.at(i) == signal_lv2_nB.at(0)){
        is_common_A = false;
        common = signal_lv2_nB.at(0);
        sig1 = signal_lv2_nB.at(1);
        ntk.foreach_fanin(ntk.get_node(signal_lv2_nA.at(0)), [&](signal sig){signal_lv2.push_back(sig);});
        if(signal_lv2.size() != 2){
          C = ntk.get_node(signal_lv2_nA.at(0));
          sig3 = signal_lv2_nA.at(0);
          signal_lv2.clear();
          ntk.foreach_fanin(ntk.get_node(signal_lv2_nA.at(1)), [&](signal sig){signal_lv2.push_back(sig);});
          if(signal_lv2.at(0) == common)
            sig2 = signal_lv2.at(1);
          else
            sig2 = signal_lv2.at(0);
        } else {
          C = ntk.get_node(signal_lv2_nA.at(1));
          sig3 = signal_lv2_nA.at(1);
          if(signal_lv2.at(0) == common)
            sig2 = signal_lv2.at(1);
          else
            sig2 = signal_lv2.at(0);
        }

      }else if(signal_lv3.at(i) == signal_lv2_nB.at(1)){
        is_common_A = false;
        common = signal_lv2_nB.at(1);
        sig1 = signal_lv2_nB.at(0);
        ntk.foreach_fanin(ntk.get_node(signal_lv2_nA.at(0)), [&](signal sig){signal_lv2.push_back(sig);});
        if(signal_lv2.size() != 2){
          C = ntk.get_node(signal_lv2_nA.at(0));
          sig3 = signal_lv2_nA.at(0);
          signal_lv2.clear();
          ntk.foreach_fanin(ntk.get_node(signal_lv2_nA.at(1)), [&](signal sig){signal_lv2.push_back(sig);});
          if(signal_lv2.at(0) == common)
            sig2 = signal_lv2.at(1);
          else
            sig2 = signal_lv2.at(0);
        } else {
          C = ntk.get_node(signal_lv2_nA.at(1));
          sig3 = signal_lv2_nA.at(1);
          if(signal_lv2.at(0) == common)
            sig2 = signal_lv2.at(1);
          else
            sig2 = signal_lv2.at(0);
        }

      }else{
        find = false;
      }
    }

    if(!find)
      return false;

    invert_outputs(n);

    if(is_common_A){
      ntk.replace_in_node(n, A, common);
      ntk.replace_in_node(B, ntk.get_node(sig3), !sig1);
      ntk.replace_in_node(C, ntk.get_node(common), sig3);
      ntk.take_out_node(A);
    } else {
      ntk.replace_in_node(n, B, common);
      ntk.replace_in_node(A, ntk.get_node(sig3), !sig1);
      ntk.replace_in_node(C, ntk.get_node(common), sig3);
      ntk.take_out_node(B);
    }

    return true;
  }

  void invert_outputs(node const& n)
  {
    std::vector<node> nodeOut;
    std::vector<signal> node_signalOut;
    ntk.foreach_node([&](node n){
      ntk.foreach_fanin(n, [&](signal sig){
        if(ntk.get_node(sig) == n){
          nodeOut.push_back(n);
          node_signalOut.push_back(sig);
        }
      });
    });

    for(int i = 0; i < node_signalOut.size(); i++){
      if(ntk.is_complemented(node_signalOut.at(i)))
        ntk.replace_in_node(nodeOut.at(i), n, node_signalOut.at(i));
      else
        ntk.replace_in_node(nodeOut.at(i), n, !node_signalOut.at(i));
    }

    std::vector<signal> signal_PO;
    ntk.foreach_po([&](signal sig){
      if(ntk.get_node(sig) == n)
        signal_PO.push_back(sig);
    });

    for(int i = 0; i < signal_PO.size(); i++){
      if(ntk.is_complemented(signal_PO.at(i)))
        ntk.replace_in_outputs(n, signal_PO.at(i));
      else
        ntk.replace_in_outputs(n, !signal_PO.at(i));
    }
  }

private:
  Ntk& ntk;
};

} // namespace detail

/* Entry point for users to call */
template<class Ntk>
void aig_algebraic_rewriting( Ntk& ntk )
{
  static_assert( std::is_same_v<typename Ntk::base_type, aig_network>, "Ntk is not an AIG" );

  depth_view dntk{ntk};
  detail::aig_algebraic_rewriting_impl p( dntk );
  p.run();
}

} /* namespace mockturtle */
